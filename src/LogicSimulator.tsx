import React, {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
} from 'react'
import {
  Copy,
  Scissors,
  ClipboardPaste,
  Trash2,
  Pencil,
  Download,
  Upload,
  RotateCcw,
  Moon,
  Sun,
  Type,
  Timer,
  Circle,
  Lightbulb,
  RotateCw,
  Crosshair,
  FileText,
  Layers,
  Maximize2,
  Minimize2,
  Power,
} from 'lucide-react'

/* =====================================================================
 *  LogicSimulator — v8
 *  ---------------------------------------------------------------------
 *  NEW IN THIS VERSION:
 *
 *   [1] UNIVERSAL MATHEMATICAL PIN PLACEMENT ENGINE
 *       Single unified formula applied to every component type:
 *
 *         N_max  = max(N_inputs, N_outputs)
 *         Height = 2 · N_max · GRID_SIZE          (spans grid nodes 0..2·N_max)
 *         Center = N_max · GRID_SIZE
 *
 *         For a side with k pins:
 *           y_i = (N_max − k + 1) + 2·i        (grid index, i = 0..k−1)
 *         Pin pixel Y = position.y + y_i · GRID_SIZE
 *
 *       Verified examples:
 *         2-in / 1-out  (N=2):  in@{1,3}, out@{2}   — output perfectly centered
 *         3-in / 2-out  (N=3):  in@{1,3,5}, out@{2,4}
 *         2-in / 3-out  (N=3):  in@{2,4}, out@{1,3,5}
 *         3-in / 4-out  (N=4):  in@{2,4,6}, out@{1,3,5,7}
 *
 *       No conditionals, no per-type padding — one formula for everyone.
 *
 *   [2] LEAD-OUT STUBS
 *       Root exactly on the box border, length = 1 · GRID_SIZE, so the
 *       tip lands precisely on the adjacent grid intersection.
 *
 *   [3] SEGMENT-BASED CORRIDOR UNFREEZING
 *       The wire preview's dynamic L-shape is checked segment-by-segment
 *       against every component's AABB.
 *         • Segment A (horizontal dog-leg)  → tested
 *         • Segment B (vertical final leg)  → tested
 *       If NEITHER segment intersects a box, the preview renders the full
 *       L-shape immediately (UNFREEZE).  Only a real segment-vs-AABB hit
 *       truncates the draft at the entry boundary.
 *       This removes the previous "stuck-forever" freeze.
 * ===================================================================== */

type PinSide = 'in' | 'out'
interface Vec2 { x: number; y: number }
interface PinRef { nodeId: string; pinId: string; side: PinSide }
type PrimitiveType =
  | 'AND' | 'OR' | 'NOT' | 'NAND' | 'NOR' | 'XOR' | 'XNOR'
  | 'INPUT' | 'OUTPUT' | 'CLOCK' | 'BUTTON'
type NodeKind = PrimitiveType | 'CHIP'

interface Pin { id: string; name: string }
interface CircuitNode {
  id: string
  kind: NodeKind
  chipId?: string
  label: string
  position: Vec2
  inputs: Pin[]
  outputs: Pin[]
  value?: boolean
  period?: number
  enabled?: boolean
  rotation?: 0 | 90 | 180 | 270
  unfolded?: boolean
  unfoldedSize?: { w: number; h: number }
  unfoldedPinPos?: { in: Vec2[]; out: Vec2[] }
}
interface Wire {
  id: string
  from: PinRef
  to: PinRef
  points?: Vec2[]
}
interface Junction {
  id: string
  wireId: string
  point: Vec2
}
interface ChipDefinition {
  id: string
  name: string
  color: string
  builtin?: boolean
  nodes: CircuitNode[]
  wires: Wire[]
  inputNodeIds: string[]
  outputNodeIds: string[]
}

type SignalMap = Record<string, boolean>
type Placement =
  | { type: 'PRIMITIVE'; kind: PrimitiveType }
  | { type: 'CHIP'; chipId: string }
  | null

interface Camera { zoom: number; offsetX: number; offsetY: number }
interface EditSession {
  chipId: string
  snapNodes: CircuitNode[]
  snapWires: Wire[]
  snapJunctions: Junction[]
  snapSelected: Set<string>
  snapCamera: Camera
}
interface HistoryEntry { nodes: CircuitNode[]; wires: Wire[]; junctions: Junction[] }
interface ContextMenuState {
  x: number
  y: number
  world: Vec2
  target: 'canvas' | 'node' | 'wire' | 'chip' | 'unfoldedChip'
  nodeId?: string
  wireId?: string
}

interface DrawSession {
  from: PinRef
  fromPos: Vec2
  points: Vec2[]
  cursor: Vec2
  preferH: boolean | null
}

const pinKey = (n: string, p: string) => `${n}:${p}`
const isPinRefEqual = (a: PinRef, b: PinRef) =>
  a.nodeId === b.nodeId && a.pinId === b.pinId && a.side === b.side

/* --------------------------- Geometry --------------------------------
 *  GRID = 16 (routing grid — pins, walls, lead-out tips all on this grid)
 *  SUB_GRID = 8 (fine snapping for wire corner bends)
 *  LEADOUT = 1 full GRID unit (stub protrudes to the adjacent grid node)
 * -------------------------------------------------------------------- */
const GRID = 16
const SUB_GRID = 8
const NODE_W_MIN = 96           // multiple of GRID
const PIN_R = 4.5
const LEADOUT = GRID            // stub length = exactly 1 grid unit
const MIN_ZOOM = 0.05
const MAX_ZOOM = 4
const WIRE_CLEARANCE = 2
const PIN_SNAP_RADIUS = 22
const WIRE_SNAP_RADIUS = 14
const WIRE_MERGE_TOL = 6

let idCounter = 0
const uid = (prefix = 'n') =>
  `${prefix}_${(idCounter++).toString(36)}_${Math.random().toString(36).slice(2, 6)}`
const clamp = (v: number, lo: number, hi: number) => Math.min(hi, Math.max(lo, v))
/** Snap to routing grid (16 px). */
const snap = (v: number) => Math.round(v / GRID) * GRID
/** Snap to sub-grid (8 px). */
const snapSub = (v: number) => Math.round(v / SUB_GRID) * SUB_GRID

function approxLabelWidth(label: string): number {
  return Math.ceil(label.length * 5.6) + 40
}

/** N_max = max(N_inputs, N_outputs, 1) — the single source of truth. */
const NmaxOf = (n: CircuitNode) =>
  Math.max(n.inputs.length, n.outputs.length, 1)

/**
 * UNIVERSAL HEIGHT FORMULA
 *   H_units = 2 · N_max         (grid intervals)
 *   height  = H_units · GRID    (pixels)
 * Box spans grid nodes y = 0 .. 2·N_max.
 * Center grid node C = N_max.
 */
const nodeHeight = (n: CircuitNode) => {
  if (n.kind === 'CHIP' && n.unfolded && n.unfoldedSize) return n.unfoldedSize.h
  const N = NmaxOf(n)
  return 2 * N * GRID
}

/**
 * Component width — rounded up to GRID so the right-edge lead-out tip
 * (box.x + box.w + LEADOUT) also lands on a grid intersection.
 */
const nodeWidth = (n: CircuitNode) => {
  if (n.kind === 'CHIP' && n.unfolded && n.unfoldedSize) return n.unfoldedSize.w
  const fromLabel = approxLabelWidth(n.label)
  let pinExtra = 0
  if (n.kind === 'CHIP') {
    const longest = Math.max(
      2,
      ...n.inputs.map((p) => p.name.length),
      ...n.outputs.map((p) => p.name.length),
    )
    pinExtra = Math.max(0, longest * 7.6)
  }
  const btnReserve =
    n.kind === 'INPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK' ? 66 : 0
  const outReserve = n.kind === 'OUTPUT' ? 40 : 0
  const raw = Math.max(NODE_W_MIN, fromLabel + btnReserve + outReserve + pinExtra)
  return Math.ceil(raw / GRID) * GRID
}
const nodeBox = (n: CircuitNode) => ({
  x: n.position.x, y: n.position.y, w: nodeWidth(n), h: nodeHeight(n),
})

/**
 * UNIVERSAL PIN PLACEMENT FORMULA
 *   For a side with k pins:
 *     y_i = (N_max − k + 1) + 2·i       (grid index, i = 0..k−1)
 *   Pin pixel position = position.y + y_i · GRID_SIZE
 * If k = 0, no pins are produced.
 *
 * The pin's outer anchor (where wires attach) is one LEADOUT beyond the
 * box wall on the pin's edge.
 */
function pinPos(n: CircuitNode, side: PinSide, index: number, count: number): Vec2 {
  if (n.kind === 'CHIP' && n.unfolded && n.unfoldedPinPos) {
    const arr = side === 'in' ? n.unfoldedPinPos.in : n.unfoldedPinPos.out
    const rel = arr[index]
    if (rel) return { x: n.position.x + rel.x, y: n.position.y + rel.y }
  }
  const b = nodeBox(n)
  const rot = n.rotation || 0
  let edge: 'left' | 'right' | 'top' | 'bottom'
  if (rot === 90) edge = side === 'in' ? 'top' : 'bottom'
  else if (rot === 180) edge = side === 'in' ? 'right' : 'left'
  else if (rot === 270) edge = side === 'in' ? 'bottom' : 'top'
  else edge = side === 'in' ? 'left' : 'right'

  const N = NmaxOf(n)
  // Universal formula: y_i = (N_max − k + 1) + 2·i
  const yIdx = (N - count + 1) + 2 * index

  if (edge === 'left' || edge === 'right') {
    const outerX = edge === 'left' ? b.x - LEADOUT : b.x + b.w + LEADOUT
    return { x: outerX, y: b.y + yIdx * GRID }
  }
  const outerY = edge === 'top' ? b.y - LEADOUT : b.y + b.h + LEADOUT
  return { x: b.x + yIdx * GRID, y: outerY }
}

/** The point on the box wall where the lead-out stub attaches. */
function pinInnerPos(n: CircuitNode, side: PinSide, index: number, count: number): Vec2 {
  const outer = pinPos(n, side, index, count)
  const b = nodeBox(n)
  const rot = n.rotation || 0
  let edge: 'left' | 'right' | 'top' | 'bottom'
  if (rot === 90) edge = side === 'in' ? 'top' : 'bottom'
  else if (rot === 180) edge = side === 'in' ? 'right' : 'left'
  else if (rot === 270) edge = side === 'in' ? 'bottom' : 'top'
  else edge = side === 'in' ? 'left' : 'right'
  if (edge === 'left') return { x: b.x, y: outer.y }
  if (edge === 'right') return { x: b.x + b.w, y: outer.y }
  if (edge === 'top') return { x: outer.x, y: b.y }
  return { x: outer.x, y: b.y + b.h }
}

const leftPinPos = (n: CircuitNode, i: number): Vec2 => pinPos(n, 'in', i, n.inputs.length)
const rightPinPos = (n: CircuitNode, i: number): Vec2 => pinPos(n, 'out', i, n.outputs.length)
const leftPinInnerPos = (n: CircuitNode, i: number): Vec2 => pinInnerPos(n, 'in', i, n.inputs.length)
const rightPinInnerPos = (n: CircuitNode, i: number): Vec2 => pinInnerPos(n, 'out', i, n.outputs.length)

interface EnumeratedPin {
  nodeId: string; pinId: string; side: PinSide; index: number
  pos: Vec2          // outer anchor (wire connection point)
  innerPos: Vec2     // box-edge anchor (lead-out base)
  node: CircuitNode
}
const enumeratePins = (n: CircuitNode): EnumeratedPin[] => {
  const list: EnumeratedPin[] = []
  n.inputs.forEach((p, i) =>
    list.push({
      nodeId: n.id, pinId: p.id, side: 'in', index: i,
      pos: leftPinPos(n, i), innerPos: leftPinInnerPos(n, i), node: n,
    }),
  )
  n.outputs.forEach((p, i) =>
    list.push({
      nodeId: n.id, pinId: p.id, side: 'out', index: i,
      pos: rightPinPos(n, i), innerPos: rightPinInnerPos(n, i), node: n,
    }),
  )
  return list
}

const hitNode = (n: CircuitNode, p: Vec2) => {
  const b = nodeBox(n)
  return p.x >= b.x && p.x <= b.x + b.w && p.y >= b.y && p.y <= b.y + b.h
}

const distToSegment = (p: Vec2, a: Vec2, b: Vec2) => {
  const dx = b.x - a.x, dy = b.y - a.y, l2 = dx * dx + dy * dy
  if (l2 === 0) return Math.hypot(p.x - a.x, p.y - a.y)
  let t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / l2
  t = Math.max(0, Math.min(1, t))
  return Math.hypot(p.x - (a.x + t * dx), p.y - (a.y + t * dy))
}

/* Factory */
const PRIMITIVE_SPEC: Record<PrimitiveType, { label: string; inputs: string[]; outputs: string[] }> = {
  AND: { label: 'AND', inputs: ['A', 'B'], outputs: ['OUT'] },
  OR: { label: 'OR', inputs: ['A', 'B'], outputs: ['OUT'] },
  NOT: { label: 'NOT', inputs: ['IN'], outputs: ['OUT'] },
  NAND: { label: 'NAND', inputs: ['A', 'B'], outputs: ['OUT'] },
  NOR: { label: 'NOR', inputs: ['A', 'B'], outputs: ['OUT'] },
  XOR: { label: 'XOR', inputs: ['A', 'B'], outputs: ['OUT'] },
  XNOR: { label: 'XNOR', inputs: ['A', 'B'], outputs: ['OUT'] },
  INPUT: { label: 'IN', inputs: [], outputs: ['OUT'] },
  OUTPUT: { label: 'OUT', inputs: ['IN'], outputs: [] },
  CLOCK: { label: 'CLK', inputs: [], outputs: ['OUT'] },
  BUTTON: { label: 'BTN', inputs: [], outputs: ['OUT'] },
}

const GATE_EDGE: Record<string, string> = {
  AND: '#059669',
  OR: '#2563eb',
  NOT: '#dc2626',
  NAND: '#0d9488',
  NOR: '#7c3aed',
  XOR: '#db2777',
  XNOR: '#ea580c',
  INPUT: '#64748b',
  OUTPUT: '#64748b',
  CLOCK: '#7c3aed',
  BUTTON: '#d97706',
}
const GATE_GLYPH: Record<string, string> = {
  AND: '∧', OR: '∨', NOT: '¬',
  NAND: '⊼', NOR: '⊽', XOR: '⊕', XNOR: '⊙',
}
const STANDARD_GATES: PrimitiveType[] = ['AND', 'OR', 'NOT', 'NAND', 'NOR', 'XOR', 'XNOR']
const IO_BLOCKS: PrimitiveType[] = ['INPUT', 'OUTPUT', 'CLOCK', 'BUTTON']

function hexToRgb(hex: string) {
  const h = hex.replace('#', '')
  const full = h.length === 3 ? h.split('').map((c) => c + c).join('') : h
  const num = parseInt(full, 16)
  return { r: (num >> 16) & 255, g: (num >> 8) & 255, b: num & 255 }
}
function shade(hex: string, amount: number) {
  const { r, g, b } = hexToRgb(hex)
  const t = amount >= 0 ? 255 : 0
  const p = Math.min(1, Math.abs(amount))
  const mix = (c: number) => Math.round(c + (t - c) * p)
  return `rgb(${mix(r)}, ${mix(g)}, ${mix(b)})`
}
function solidFill(edgeColor: string | undefined, dark: boolean, fallback: string) {
  if (!edgeColor) return fallback
  return dark ? shade(edgeColor, -0.32) : shade(edgeColor, 0.86)
}

const makePins = (names: string[]): Pin[] =>
  names.map((name) => ({ id: name.toLowerCase(), name }))

function createPrimitiveNode(kind: PrimitiveType, position: Vec2, label?: string): CircuitNode {
  const spec = PRIMITIVE_SPEC[kind]
  return {
    id: uid(kind.toLowerCase()),
    kind,
    label: label ?? spec.label,
    position,
    inputs: makePins(spec.inputs),
    outputs: makePins(spec.outputs),
    ...(kind === 'INPUT' || kind === 'BUTTON' ? { value: false } : {}),
    ...(kind === 'CLOCK' ? { period: 30, value: false, enabled: true } : {}),
  }
}

function labelOfNode(nodes: CircuitNode[], id: string) {
  return nodes.find((n) => n.id === id)?.label ?? ''
}

function createChipNode(chip: ChipDefinition, position: Vec2): CircuitNode {
  return {
    id: uid('chip'),
    kind: 'CHIP',
    chipId: chip.id,
    label: chip.name,
    position,
    inputs: chip.inputNodeIds.map((nid, i) => ({
      id: `i${i}`,
      name: labelOfNode(chip.nodes, nid) || `IN${i}`,
    })),
    outputs: chip.outputNodeIds.map((nid, i) => ({
      id: `o${i}`,
      name: labelOfNode(chip.nodes, nid) || `OUT${i}`,
    })),
  }
}

function refreshChipInstance(node: CircuitNode, chip: ChipDefinition): CircuitNode {
  return {
    ...node,
    label: chip.name,
    inputs: chip.inputNodeIds.map((nid, i) => ({
      id: `i${i}`,
      name: labelOfNode(chip.nodes, nid) || `IN${i}`,
    })),
    outputs: chip.outputNodeIds.map((nid, i) => ({
      id: `o${i}`,
      name: labelOfNode(chip.nodes, nid) || `OUT${i}`,
    })),
  }
}

const createWire = (from: PinRef, to: PinRef, points?: Vec2[]): Wire =>
  ({ id: uid('w'), from, to, ...(points && points.length >= 2 ? { points } : {}) })

/* Built-ins */
const outRef = (id: string, pin: string): PinRef => ({ nodeId: id, pinId: pin, side: 'out' })
const inRef = (id: string, pin: string): PinRef => ({ nodeId: id, pinId: pin, side: 'in' })
const U = (col: number, row: number): Vec2 => ({ x: col * 160, y: row * 120 })

function buildRsLatch(): ChipDefinition {
  const R = createPrimitiveNode('INPUT', U(0, 0), 'R')
  const S = createPrimitiveNode('INPUT', U(0, 2), 'S')
  const orQ = createPrimitiveNode('NOR', U(2, 0), 'NOR')
  const orQb = createPrimitiveNode('NOR', U(2, 2), 'NOR')
  const qN = createPrimitiveNode('NOT', U(3.5, 0), '¬')
  const qN2 = createPrimitiveNode('NOT', U(3.5, 2), '¬')
  const Q = createPrimitiveNode('OUTPUT', U(5.5, 0), 'Q')
  const Qbar = createPrimitiveNode('OUTPUT', U(5.5, 2), "Q'")
  return {
    id: 'builtin-rs-latch', name: 'RS Latch', color: '#0ea5e9', builtin: true,
    inputNodeIds: [R.id, S.id], outputNodeIds: [Q.id, Qbar.id],
    nodes: [R, S, orQ, orQb, qN, qN2, Q, Qbar],
    wires: [
      createWire(outRef(R.id, 'out'), inRef(orQ.id, 'a')),
      createWire(outRef(qN2.id, 'out'), inRef(orQ.id, 'b')),
      createWire(outRef(S.id, 'out'), inRef(orQb.id, 'a')),
      createWire(outRef(qN.id, 'out'), inRef(orQb.id, 'b')),
      createWire(outRef(orQ.id, 'out'), inRef(qN.id, 'in')),
      createWire(outRef(orQb.id, 'out'), inRef(qN2.id, 'in')),
      createWire(outRef(qN.id, 'out'), inRef(Q.id, 'in')),
      createWire(outRef(qN2.id, 'out'), inRef(Qbar.id, 'in')),
    ],
  }
}

function buildDLatch(rs: ChipDefinition): ChipDefinition {
  const D = createPrimitiveNode('INPUT', U(0, 0), 'D')
  const EN = createPrimitiveNode('INPUT', U(0, 4), 'EN')
  const nD = createPrimitiveNode('NOT', U(1.5, 0), '¬')
  const andS = createPrimitiveNode('AND', U(3, 0), 'D·EN')
  const andR = createPrimitiveNode('AND', U(3, 2), '¬D·EN')
  const latch = createChipNode(rs, U(5, 0))
  const Q = createPrimitiveNode('OUTPUT', U(7.5, 0), 'Q')
  const Qbar = createPrimitiveNode('OUTPUT', U(7.5, 2), "Q'")
  return {
    id: 'builtin-d-latch', name: 'D Latch', color: '#8b5cf6', builtin: true,
    inputNodeIds: [D.id, EN.id], outputNodeIds: [Q.id, Qbar.id],
    nodes: [D, EN, nD, andS, andR, latch, Q, Qbar],
    wires: [
      createWire(outRef(D.id, 'out'), inRef(nD.id, 'in')),
      createWire(outRef(D.id, 'out'), inRef(andS.id, 'a')),
      createWire(outRef(nD.id, 'out'), inRef(andR.id, 'a')),
      createWire(outRef(EN.id, 'out'), inRef(andS.id, 'b')),
      createWire(outRef(EN.id, 'out'), inRef(andR.id, 'b')),
      createWire(outRef(andS.id, 'out'), inRef(latch.id, 'i1')),
      createWire(outRef(andR.id, 'out'), inRef(latch.id, 'i0')),
      createWire(outRef(latch.id, 'o0'), inRef(Q.id, 'in')),
      createWire(outRef(latch.id, 'o1'), inRef(Qbar.id, 'in')),
    ],
  }
}

function makeBuiltInChips(): ChipDefinition[] {
  const rs = buildRsLatch()
  return [rs, buildDLatch(rs)]
}

/* =====================================================================
 *  UNION-FIND NET SOLVER
 * ===================================================================== */

class UnionFind {
  private parent = new Map<string, string>()
  find(x: string): string {
    const p = this.parent.get(x)
    if (p === undefined) { this.parent.set(x, x); return x }
    if (p === x) return x
    const root = this.find(p)
    this.parent.set(x, root)
    return root
  }
  union(a: string, b: string) {
    const ra = this.find(a), rb = this.find(b)
    if (ra !== rb) this.parent.set(ra, rb)
  }
}

interface FlattenedGate {
  key: string
  type: 'AND' | 'OR' | 'NOT' | 'NAND' | 'NOR' | 'XOR' | 'XNOR'
  inputKeys: string[]
  outputKey: string
}

interface NetModel {
  terminalNet: Map<string, string>
  allTerminals: Set<string>
  gates: FlattenedGate[]
  sourceKeys: Set<string>
}

const snapWirePoint = (p: Vec2): Vec2 => ({ x: snapSub(p.x), y: snapSub(p.y) })

function collapsePolyline(points: Vec2[], epsilon = 0.75): Vec2[] {
  if (points.length <= 2) return points.map((p) => ({ ...p }))
  const out: Vec2[] = []
  for (const p of points) {
    const last = out[out.length - 1]
    if (last && Math.hypot(p.x - last.x, p.y - last.y) <= epsilon) continue
    out.push({ ...p })
    while (out.length >= 3) {
      const a = out[out.length - 3]
      const b = out[out.length - 2]
      const c = out[out.length - 1]
      const cross = (b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x)
      const ab = Math.hypot(b.x - a.x, b.y - a.y)
      const bc = Math.hypot(c.x - b.x, c.y - b.y)
      if (Math.abs(cross) <= epsilon * Math.max(1, ab + bc)) out.splice(out.length - 2, 1)
      else break
    }
  }
  return out
}

function ensureOrthogonalPolyline(points: Vec2[]): Vec2[] {
  if (points.length < 2) return points.map((p) => ({ ...p }))
  const out: Vec2[] = [{ ...points[0] }]
  for (let i = 1; i < points.length; i++) {
    const target = { ...points[i] }
    const last = out[out.length - 1]
    if (last.x !== target.x && last.y !== target.y) {
      const corner = Math.abs(target.x - last.x) >= Math.abs(target.y - last.y)
        ? { x: target.x, y: last.y }
        : { x: last.x, y: target.y }
      out.push(corner)
    }
    out.push(target)
  }
  return collapsePolyline(out)
}

function anchorOf(
  nodeId: string, pinId: string, side: PinSide,
  nodes: CircuitNode[], junctions: Junction[],
): Vec2 | null {
  const j = junctions.find((x) => x.id === nodeId)
  if (j) return j.point
  const n = nodes.find((x) => x.id === nodeId)
  if (!n) return null
  return pinAnchor(n, { side, pinId })
}

function pinAnchor(n: CircuitNode, w: { side: PinSide; pinId: string }): Vec2 | null {
  if (w.side === 'out') {
    const i = n.outputs.findIndex((p) => p.id === w.pinId)
    return i >= 0 ? rightPinPos(n, i) : null
  }
  const i = n.inputs.findIndex((p) => p.id === w.pinId)
  return i >= 0 ? leftPinPos(n, i) : null
}

function wireView(w: Wire, nodes: CircuitNode[], junctions: Junction[]): { pts: Vec2[] } | null {
  const a = anchorOf(w.from.nodeId, w.from.pinId, w.from.side, nodes, junctions)
  const b = anchorOf(w.to.nodeId, w.to.pinId, w.to.side, nodes, junctions)
  if (!a || !b) return null
  const stored = w.points?.length ? w.points : [a, b]
  const pts = stored.map(snapWirePoint)
  pts[0] = { ...a }
  pts[pts.length - 1] = { ...b }
  return { pts: ensureOrthogonalPolyline(pts) }
}

function flattenGates(
  nodes: CircuitNode[], prefix: string,
  chips: Record<string, ChipDefinition>, depth: number,
  acc: FlattenedGate[],
) {
  if (depth > 16) return
  for (const n of nodes) {
    const id = prefix + n.id
    if (n.kind === 'CHIP' && n.chipId) {
      const chip = chips[n.chipId]
      if (!chip) continue
      flattenGates(chip.nodes, `${id}/`, chips, depth + 1, acc)
    } else if (['AND', 'OR', 'NOT', 'NAND', 'NOR', 'XOR', 'XNOR'].includes(n.kind)) {
      acc.push({
        key: id,
        type: n.kind as any,
        inputKeys: n.inputs.map((p) => pinKey(id, p.id)),
        outputKey: pinKey(id, n.outputs[0].id),
      })
    }
  }
}

function buildNetModel(
  nodes: CircuitNode[],
  wires: Wire[],
  junctions: Junction[],
  chips: Record<string, ChipDefinition>,
): NetModel {
  const uf = new UnionFind()
  const allTerminals = new Set<string>()

  const touch = (key: string) => { uf.find(key); allTerminals.add(key) }

  for (const n of nodes) {
    for (const p of n.inputs) touch(pinKey(n.id, p.id))
    for (const p of n.outputs) touch(pinKey(n.id, p.id))
  }

  for (const w of wires) {
    const fromKey = pinKey(w.from.nodeId, w.from.pinId)
    const toKey = pinKey(w.to.nodeId, w.to.pinId)
    touch(fromKey); touch(toKey)
    uf.union(fromKey, toKey)
  }

  for (const j of junctions) {
    touch(j.id)
    const w = wires.find((x) => x.id === j.wireId)
    if (w) {
      const anchorKey = pinKey(w.from.nodeId, w.from.pinId)
      touch(anchorKey)
      uf.union(j.id, anchorKey)
    }
  }

  const wireGeom: { w: Wire; pts: Vec2[] }[] = []
  for (const w of wires) {
    const vw = wireView(w, nodes, junctions)
    if (vw) wireGeom.push({ w, pts: vw.pts })
  }
  for (const w of wires) {
    const fromPos = anchorOf(w.from.nodeId, w.from.pinId, w.from.side, nodes, junctions)
    const toPos = anchorOf(w.to.nodeId, w.to.pinId, w.to.side, nodes, junctions)
    const wFromKey = pinKey(w.from.nodeId, w.from.pinId)
    const wToKey = pinKey(w.to.nodeId, w.to.pinId)
    for (const other of wireGeom) {
      if (other.w.id === w.id) continue
      const otherKey = pinKey(other.w.from.nodeId, other.w.from.pinId)
      if (otherKey === wFromKey || otherKey === wToKey) continue
      if (fromPos) {
        for (let i = 0; i < other.pts.length - 1; i++) {
          if (distToSegment(fromPos, other.pts[i], other.pts[i + 1]) <= WIRE_MERGE_TOL) {
            touch(otherKey)
            uf.union(wFromKey, otherKey)
            break
          }
        }
      }
      if (toPos) {
        for (let i = 0; i < other.pts.length - 1; i++) {
          if (distToSegment(toPos, other.pts[i], other.pts[i + 1]) <= WIRE_MERGE_TOL) {
            touch(otherKey)
            uf.union(wToKey, otherKey)
            break
          }
        }
      }
    }
  }

  const anchors: { key: string; pos: Vec2 }[] = []
  for (const n of nodes) {
    for (const pin of enumeratePins(n)) {
      anchors.push({ key: pinKey(pin.nodeId, pin.pinId), pos: pin.pos })
    }
  }
  for (let i = 0; i < anchors.length; i++) {
    for (let k = i + 1; k < anchors.length; k++) {
      const a = anchors[i], b = anchors[k]
      if (Math.abs(a.pos.x - b.pos.x) <= 1 && Math.abs(a.pos.y - b.pos.y) <= 1) {
        uf.union(a.key, b.key)
      }
    }
  }

  function linkChip(node: CircuitNode, depth: number) {
    if (depth > 16) return
    if (node.kind !== 'CHIP' || !node.chipId) return
    const chip = chips[node.chipId]
    if (!chip) return
    chip.inputNodeIds.forEach((innerId, i) => {
      const innerNode = chip.nodes.find((x) => x.id === innerId)
      if (!innerNode || !innerNode.outputs[0]) return
      const outerKey = pinKey(node.id, `i${i}`)
      const innerKey = pinKey(`${node.id}/${innerId}`, innerNode.outputs[0].id)
      touch(outerKey); touch(innerKey)
      uf.union(outerKey, innerKey)
    })
    chip.outputNodeIds.forEach((innerId, i) => {
      const innerNode = chip.nodes.find((x) => x.id === innerId)
      if (!innerNode || !innerNode.inputs[0]) return
      const outerKey = pinKey(node.id, `o${i}`)
      const innerKey = pinKey(`${node.id}/${innerId}`, innerNode.inputs[0].id)
      touch(outerKey); touch(innerKey)
      uf.union(outerKey, innerKey)
    })
    for (const iw of chip.wires) {
      const fromKey = pinKey(`${node.id}/${iw.from.nodeId}`, iw.from.pinId)
      const toKey = pinKey(`${node.id}/${iw.to.nodeId}`, iw.to.pinId)
      touch(fromKey); touch(toKey)
      uf.union(fromKey, toKey)
    }
    for (const innerNode of chip.nodes) {
      for (const p of innerNode.inputs) touch(pinKey(`${node.id}/${innerNode.id}`, p.id))
      for (const p of innerNode.outputs) touch(pinKey(`${node.id}/${innerNode.id}`, p.id))
      if (innerNode.kind === 'CHIP') linkChip(
        { ...innerNode, id: `${node.id}/${innerNode.id}` }, depth + 1,
      )
    }
  }
  for (const n of nodes) if (n.kind === 'CHIP') linkChip(n, 0)

  const terminalNet = new Map<string, string>()
  for (const key of allTerminals) terminalNet.set(key, uf.find(key))

  const gates: FlattenedGate[] = []
  flattenGates(nodes, '', chips, 0, gates)

  const sourceKeys = new Set<string>()
  function collectSources(ns: CircuitNode[], prefix: string, depth: number) {
    if (depth > 16) return
    for (const n of ns) {
      const id = prefix + n.id
      if (n.kind === 'INPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK') {
        const key = pinKey(id, n.outputs[0].id)
        sourceKeys.add(key)
        touch(key)
        terminalNet.set(key, uf.find(key))
      } else if (n.kind === 'CHIP' && n.chipId) {
        const chip = chips[n.chipId]
        if (chip) collectSources(chip.nodes, `${id}/`, depth + 1)
      }
    }
  }
  collectSources(nodes, '', 0)

  return { terminalNet, allTerminals, gates, sourceKeys }
}

/* =====================================================================
 *  SIMULATOR
 * ===================================================================== */

const SETTLE_PASSES = 200
const SIM_TPS = 60

class Simulator {
  private netValues = new Map<string, boolean>()
  private model: NetModel | null = null
  private tickCount = 0

  load(model: NetModel) {
    this.model = model
    const next = new Map<string, boolean>()
    for (const root of new Set(model.terminalNet.values())) {
      next.set(root, this.netValues.get(root) ?? false)
    }
    this.netValues = next
  }

  reset() {
    this.netValues.clear()
    this.tickCount = 0
  }

  private readNet(root: string | undefined): boolean {
    if (!root) return false
    return this.netValues.get(root) ?? false
  }

  private evalGate(type: FlattenedGate['type'], a: boolean, b: boolean): boolean {
    switch (type) {
      case 'AND': return a && b
      case 'OR': return a || b
      case 'NOT': return !a
      case 'NAND': return !(a && b)
      case 'NOR': return !(a || b)
      case 'XOR': return a !== b
      case 'XNOR': return a === b
    }
  }

  tick(nodes: CircuitNode[]) {
    const model = this.model
    if (!model) return
    this.tickCount++

    for (const root of new Set(model.terminalNet.values())) {
      this.netValues.set(root, false)
    }

    for (const n of nodes) {
      if (n.kind === 'INPUT' || n.kind === 'BUTTON') {
        const key = pinKey(n.id, n.outputs[0]?.id ?? 'out')
        const root = model.terminalNet.get(key)
        if (root && n.value) this.netValues.set(root, true)
      } else if (n.kind === 'CLOCK') {
        const key = pinKey(n.id, n.outputs[0]?.id ?? 'out')
        const root = model.terminalNet.get(key)
        if (root) {
          if (n.enabled === false) {
            this.netValues.set(root, false)
          } else {
            const period = Math.max(2, n.period ?? 30)
            const half = Math.floor(period / 2)
            const high = (this.tickCount % period) < half
            if (high) this.netValues.set(root, true)
          }
        }
      }
    }

    for (let pass = 0; pass < SETTLE_PASSES; pass++) {
      let changed = false
      const snapshot = new Map(this.netValues)
      for (const g of model.gates) {
        const inRoots = g.inputKeys.map((k) => model.terminalNet.get(k))
        const a = this.readNet(inRoots[0])
        const b = inRoots.length > 1 ? this.readNet(inRoots[1]) : false
        const value = this.evalGate(g.type, a, b)
        if (!value) continue
        const outRoot = model.terminalNet.get(g.outputKey)
        if (!outRoot) continue
        if (!snapshot.get(outRoot)) {
          this.netValues.set(outRoot, true)
          changed = true
        }
      }
      if (!changed) break
    }
  }

  snapshot(): SignalMap {
    const out: SignalMap = {}
    const model = this.model
    if (!model) return out
    for (const key of model.allTerminals) {
      const root = model.terminalNet.get(key)
      out[key] = root ? (this.netValues.get(root) ?? false) : false
    }
    return out
  }
}

/* Packaging */
const CHIP_COLORS = [
  '#2563eb', '#059669', '#d97706', '#dc2626', '#7c3aed',
  '#0891b2', '#be185d', '#4f46e5', '#0d9488', '#b45309',
]

function packageSelectionInto(
  name: string, color: string,
  nodes: CircuitNode[], wires: Wire[], selected: Set<string>, existingId?: string,
): ChipDefinition | null {
  const sel = nodes.filter((n) => selected.has(n.id))
  if (!sel.length) return null
  const ids = new Set(sel.map((n) => n.id))
  const inputs = sel.filter((n) => n.kind === 'INPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK')
    .sort((a, b) => a.position.y - b.position.y)
  const outputs = sel.filter((n) => n.kind === 'OUTPUT').sort((a, b) => a.position.y - b.position.y)
  if (!inputs.length || !outputs.length) return null
  return {
    id: existingId ?? uid('chip'), name, color, builtin: false,
    inputNodeIds: inputs.map((n) => n.id), outputNodeIds: outputs.map((n) => n.id),
    nodes: sel, wires: wires.filter((w) => ids.has(w.from.nodeId) && ids.has(w.to.nodeId)),
  }
}
function centroidOf(nodes: CircuitNode[]): Vec2 {
  if (!nodes.length) return { x: 0, y: 0 }
  const s = nodes.reduce((a, n) => ({ x: a.x + n.position.x, y: a.y + n.position.y }), { x: 0, y: 0 })
  return { x: Math.round(s.x / nodes.length), y: Math.round(s.y / nodes.length) }
}

/* Theme */
interface Theme {
  bg: string; grid: string; wireHigh: string; wireLow: string; wireHover: string
  pinHigh: string; pinLow: string; body: string; edge: string; label: string; sel: string
}
const LIGHT: Theme = {
  bg: '#f1f5f9', grid: '#cbd5e1', wireHigh: '#2563eb', wireLow: '#64748b', wireHover: '#94a3b8',
  pinHigh: '#2563eb', pinLow: '#94a3b8', body: '#ffffff', edge: '#1e293b', label: '#0f172a', sel: '#2563eb',
}
const DARK: Theme = {
  bg: '#0b0b0d', grid: '#2a2a2e', wireHigh: '#38bdf8', wireLow: '#9ca3af', wireHover: '#d1d5db',
  pinHigh: '#38bdf8', pinLow: '#9ca3af', body: '#3f3f46', edge: '#e4e4e7', label: '#fafafa', sel: '#38bdf8',
}

/* Renderer */
const roundRect = (ctx: CanvasRenderingContext2D, x: number, y: number, w: number, h: number, r: number) => {
  ctx.beginPath()
  ctx.moveTo(x + r, y)
  ctx.arcTo(x + w, y, x + w, y + h, r)
  ctx.arcTo(x + w, y + h, x, y + h, r)
  ctx.arcTo(x, y + h, x, y, r)
  ctx.arcTo(x, y, x + w, y, r)
  ctx.closePath()
}

function drawGrid(ctx: CanvasRenderingContext2D, left: number, top: number, right: number, bottom: number, zoom: number, color: string) {
  ctx.fillStyle = color
  const r = clamp(1.1 / zoom, 0.55, 1.4)
  const x0 = Math.floor(left / GRID) * GRID
  const y0 = Math.floor(top / GRID) * GRID
  for (let x = x0; x < right; x += GRID)
    for (let y = y0; y < bottom; y += GRID) {
      ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill()
    }
}

function projectOnSegment(p: Vec2, a: Vec2, b: Vec2) {
  const dx = b.x - a.x, dy = b.y - a.y
  const l2 = dx * dx + dy * dy
  if (l2 === 0) {
    const d = Math.hypot(p.x - a.x, p.y - a.y)
    return { point: { x: a.x, y: a.y }, dist: d, t: 0 }
  }
  let t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / l2
  t = Math.max(0, Math.min(1, t))
  const point = { x: a.x + t * dx, y: a.y + t * dy }
  return { point, dist: Math.hypot(p.x - point.x, p.y - point.y), t }
}

function snapPointToSegment(p: Vec2, a: Vec2, b: Vec2): Vec2 {
  const horizontal = Math.abs(a.y - b.y) <= 0.5
  if (horizontal) {
    const x = clamp(snapSub(p.x), Math.min(a.x, b.x), Math.max(a.x, b.x))
    return { x, y: a.y }
  }
  const y = clamp(snapSub(p.y), Math.min(a.y, b.y), Math.max(a.y, b.y))
  return { x: a.x, y }
}

function orthogonalPathTo(points: Vec2[], next: Vec2, preferH: boolean | null = null): Vec2[] {
  if (!points.length) return [snapWirePoint(next)]

  const base = collapsePolyline(points.map(snapWirePoint))
  const last = base[base.length - 1]
  const target = snapWirePoint(next)
  const dx = target.x - last.x
  const dy = target.y - last.y

  if (dx === 0 || dy === 0) return collapsePolyline([...base, target])

  let useH: boolean
  if (preferH !== null) {
    useH = preferH
  } else if (base.length >= 2) {
    const prev = base[base.length - 2]
    useH = Math.abs(prev.y - last.y) <= 0.5
  } else {
    useH = Math.abs(dx) >= Math.abs(dy)
  }

  const corner = useH
    ? { x: target.x, y: last.y }
    : { x: last.x, y: target.y }
  return collapsePolyline([...base, corner, target])
}

function addOrthogonalAnchor(points: Vec2[], next: Vec2, preferH: boolean | null = null): Vec2[] {
  return orthogonalPathTo(points, next, preferH)
}

/* ---------------------------------------------------------------------
 *  LINE-SEGMENT vs AABB (slab method)
 *  Returns the FIRST entry point along a→b, with parameter t ∈ [0,1],
 *  or null if the segment never enters the box.
 * ------------------------------------------------------------------- */
function segmentAABBIntersect(
  a: Vec2, b: Vec2,
  box: { x: number; y: number; w: number; h: number },
): { pt: Vec2; t: number } | null {
  const minX = box.x
  const maxX = box.x + box.w
  const minY = box.y
  const maxY = box.y + box.h

  // If the start point is already inside the box, return immediately.
  if (a.x >= minX && a.x <= maxX && a.y >= minY && a.y <= maxY) {
    return { pt: { x: a.x, y: a.y }, t: 0 }
  }

  const dx = b.x - a.x
  const dy = b.y - a.y

  let tmin = 0
  let tmax = 1
  const p = [-dx, dx, -dy, dy]
  const q = [a.x - minX, maxX - a.x, a.y - minY, maxY - a.y]

  for (let i = 0; i < 4; i++) {
    if (p[i] === 0) {
      if (q[i] < 0) return null
    } else {
      const t = q[i] / p[i]
      if (p[i] < 0) {
        if (t > tmin) tmin = t
      } else {
        if (t < tmax) tmax = t
      }
    }
  }

  if (tmin > tmax) return null
  return { pt: { x: a.x + tmin * dx, y: a.y + tmin * dy }, t: tmin }
}

/** Is the point inside any node's rectangle (with clearance)? */
function pointInAnyNode(p: Vec2, nodes: CircuitNode[], ignoreIds?: Set<string>): boolean {
  for (const n of nodes) {
    if (ignoreIds?.has(n.id)) continue
    const b = nodeBox(n)
    if (
      p.x >= b.x - WIRE_CLEARANCE &&
      p.x <= b.x + b.w + WIRE_CLEARANCE &&
      p.y >= b.y - WIRE_CLEARANCE &&
      p.y <= b.y + b.h + WIRE_CLEARANCE
    ) return true
  }
  return false
}

/**
 * SEGMENT-BASED CORRIDOR TRUNCATION.
 * Takes a proposed polyline starting at `pts[0]` and walks segments one
 * by one, testing each against every component AABB.  The first segment
 * that hits a box is truncated at the entry boundary point (pulled back
 * a hair so the endpoint is strictly outside); any remaining segments
 * are dropped.
 *
 * When no segment hits, the WHOLE polyline is preserved → the preview
 * renders the full L-shape (this is the "unfreeze" behaviour).
 */
function truncatePolylineOnCollision(
  pts: Vec2[],
  nodes: CircuitNode[],
  ignoreNodeId?: string,
): Vec2[] {
  if (pts.length < 2) return pts.map((p) => ({ ...p }))
  const out: Vec2[] = [{ ...pts[0] }]

  for (let i = 1; i < pts.length; i++) {
    const a = out[out.length - 1]
    const b = pts[i]
    let best: { pt: Vec2; t: number } | null = null

    for (const n of nodes) {
      if (n.id === ignoreNodeId) continue
      const box = nodeBox(n)
      const inflated = {
        x: box.x - WIRE_CLEARANCE,
        y: box.y - WIRE_CLEARANCE,
        w: box.w + 2 * WIRE_CLEARANCE,
        h: box.h + 2 * WIRE_CLEARANCE,
      }
      const hit = segmentAABBIntersect(a, b, inflated)
      if (hit && hit.t > 1e-3 && (!best || hit.t < best.t)) best = hit
    }

    if (best) {
      const dx = b.x - a.x
      const dy = b.y - a.y
      const len = Math.hypot(dx, dy) || 1
      const back = 0.5
      out.push({
        x: best.pt.x - (dx / len) * back,
        y: best.pt.y - (dy / len) * back,
      })
      return out
    }
    out.push({ ...b })
  }
  return out
}

/**
 * Build the dynamic preview polyline for an active wire draft:
 *   fixedPoints = committed polyline so far (starts at fromPos)
 *   mouse       = current raw cursor position (world)
 *   preferH     = forced first-segment direction, or null for auto
 *
 * The L-shape (dog-leg + final leg) is then run through the segment
 * collision engine.  If neither of the two dynamic segments hits a box,
 * the full L-shape is returned unchanged — this is the "unfreeze".
 */
function buildPreviewPolyline(
  fixedPoints: Vec2[],
  mouse: Vec2,
  preferH: boolean | null,
  nodes: CircuitNode[],
  ignoreNodeId: string,
): Vec2[] {
  const last = fixedPoints[fixedPoints.length - 1]
  const target = snapWirePoint(mouse)
  const dx = target.x - last.x
  const dy = target.y - last.y

  // Degenerate: straight horizontal or vertical.
  if (Math.abs(dx) <= 0.5 || Math.abs(dy) <= 0.5) {
    const raw = [{ ...last }, target]
    return truncatePolylineOnCollision(raw, nodes, ignoreNodeId)
  }

  // Choose first-segment orientation.
  let useH: boolean
  if (preferH !== null) useH = preferH
  else if (fixedPoints.length >= 2) {
    const prev = fixedPoints[fixedPoints.length - 2]
    useH = Math.abs(prev.y - last.y) <= 0.5
  } else {
    useH = Math.abs(dx) >= Math.abs(dy)
  }

  const corner = useH
    ? { x: target.x, y: last.y }
    : { x: last.x, y: target.y }

  const raw = [{ ...last }, corner, target]
  return truncatePolylineOnCollision(raw, nodes, ignoreNodeId)
}

function drawBody(
  ctx: CanvasRenderingContext2D, n: CircuitNode,
  fill: string, edge: string | null,
  selected: boolean, zoom: number, theme: Theme,
) {
  const b = nodeBox(n)
  const r = 4
  if (selected) {
    ctx.save()
    ctx.strokeStyle = theme.sel
    ctx.lineWidth = 2.8 / zoom
    roundRect(ctx, b.x - 3.5, b.y - 3.5, b.w + 7, b.h + 7, r + 2)
    ctx.stroke(); ctx.restore()
  }
  ctx.fillStyle = fill
  roundRect(ctx, b.x, b.y, b.w, b.h, r); ctx.fill()
  ctx.strokeStyle = edge ?? theme.edge
  ctx.lineWidth = 1.6
  roundRect(ctx, b.x, b.y, b.w, b.h, r); ctx.stroke()
}

function drawNode(
  ctx: CanvasRenderingContext2D, n: CircuitNode, selected: boolean,
  signal: SignalMap, chipMeta: Record<string, { color: string }>,
  zoom: number, theme: Theme, dark: boolean, alpha = 1,
) {
  ctx.save()
  ctx.globalAlpha = alpha
  const b = nodeBox(n)
  const fill = solidFill(GATE_EDGE[n.kind], dark, theme.body)
  const edge = GATE_EDGE[n.kind] ?? null

  if (n.kind === 'INPUT' || n.kind === 'CLOCK' || n.kind === 'BUTTON') {
    drawBody(ctx, n, fill, edge, selected, zoom, theme)
    const value = (n.kind === 'CLOCK')
      ? (n.enabled === false ? false : !!signal[pinKey(n.id, 'out')])
      : !!n.value
    const btnW = 48
    const btnH = Math.min(26, b.h - 6)
    const nw = nodeWidth(n)
    const bx = n.position.x + nw - btnW - 14
    const by = n.position.y + (b.h - btnH) / 2
    const disabled = n.kind === 'CLOCK' && n.enabled === false
    ctx.fillStyle = value ? theme.wireHigh : (dark ? '#3f3f46' : '#e2e8f0')
    roundRect(ctx, bx, by, btnW, btnH, 4); ctx.fill()
    ctx.strokeStyle = value ? theme.wireHigh : (dark ? '#a1a1aa' : theme.pinLow); ctx.lineWidth = 1.2; ctx.stroke()
    ctx.fillStyle = value ? '#fff' : theme.label
    ctx.font = '700 10px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle'
    const txt = n.kind === 'CLOCK'
      ? (disabled ? 'OFF' : `${(60 / Math.max(2, n.period ?? 30)).toFixed(1)}Hz`)
      : n.kind === 'BUTTON' ? (value ? 'HOLD' : 'BTN')
        : (value ? 'ON' : 'OFF')
    ctx.fillText(txt, bx + btnW / 2, by + btnH / 2 + 0.5)
    ctx.fillStyle = theme.label
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'left'
    ctx.save()
    ctx.beginPath()
    ctx.rect(n.position.x + 8, n.position.y, bx - n.position.x - 12, b.h)
    ctx.clip()
    ctx.fillText(n.label, n.position.x + 12, n.position.y + b.h / 2)
    ctx.restore()
    ctx.restore()
    return
  }

  if (n.kind === 'OUTPUT') {
    drawBody(ctx, n, fill, edge, selected, zoom, theme)
    const value = !!signal[pinKey(n.id, n.inputs[0]?.id ?? 'in')]
    const nw = nodeWidth(n)
    const cy = n.position.y + b.h / 2
    const bulbCx = n.position.x + nw - 22
    const labelMaxWidth = nw - 22 - 44
    if (value) { ctx.save(); ctx.shadowColor = theme.wireHigh + '80'; ctx.shadowBlur = 14 }
    ctx.beginPath()
    ctx.arc(bulbCx, cy - 2, 8, 0, Math.PI * 2)
    ctx.fillStyle = value ? theme.wireHigh : (dark ? '#334155' : '#cbd5e1'); ctx.fill()
    ctx.strokeStyle = value ? theme.wireHigh : theme.pinLow; ctx.lineWidth = 1.5; ctx.stroke()
    ctx.beginPath()
    ctx.moveTo(bulbCx - 4.5, cy + 6.5); ctx.lineTo(bulbCx + 4.5, cy + 6.5)
    ctx.lineTo(bulbCx + 3, cy + 10); ctx.lineTo(bulbCx - 3, cy + 10)
    ctx.closePath()
    ctx.fillStyle = value ? theme.wireHigh : (dark ? '#475569' : '#94a3b8')
    ctx.fill()
    if (value) ctx.restore()
    ctx.fillStyle = theme.label
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'left'; ctx.textBaseline = 'middle'
    ctx.save()
    ctx.beginPath()
    ctx.rect(n.position.x + 8, n.position.y, labelMaxWidth, b.h)
    ctx.clip()
    ctx.fillText(n.label, n.position.x + 12, cy)
    ctx.restore()
    ctx.restore()
    return
  }

  if (n.kind === 'CHIP') {
    const meta = n.chipId ? chipMeta[n.chipId] : undefined
    const col = meta?.color ?? '#6366f1'
    const fillC = solidFill(col, dark, theme.body)
    drawBody(ctx, n, fillC, col, selected, zoom, theme)
    const nw = nodeWidth(n)
    ctx.fillStyle = theme.label
    ctx.font = '500 9px ui-sans-serif, system-ui, sans-serif'
    ctx.textBaseline = 'middle'
    n.inputs.forEach((p, i) => {
      ctx.textAlign = 'left'
      ctx.fillText(p.name, n.position.x + 10, leftPinPos(n, i).y)
    })
    n.outputs.forEach((p, i) => {
      ctx.textAlign = 'right'
      ctx.fillText(p.name, n.position.x + nw - 10, rightPinPos(n, i).y)
    })
    ctx.fillStyle = theme.label
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'
    ctx.fillText(n.label, n.position.x + b.w / 2, n.position.y + b.h / 2 + 2)
    ctx.restore()
    return
  }

  // Standard gate — glyph + label scaled to box height.
  drawBody(ctx, n, fill, edge, selected, zoom, theme)
  const cx = n.position.x + b.w / 2
  const labelY = n.position.y + Math.min(14, b.h * 0.28)
  const glyphY = n.position.y + b.h * 0.58
  const glyphSize = Math.min(26, b.h * 0.55)
  const labelSize = Math.max(8, Math.min(10, b.h * 0.22))
  const glyph = GATE_GLYPH[n.kind] ?? '?'
  ctx.fillStyle = edge ?? theme.edge
  ctx.font = `800 ${glyphSize}px ui-sans-serif, system-ui, sans-serif`
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle'
  ctx.fillText(glyph, cx, glyphY)
  ctx.fillStyle = theme.label
  ctx.font = `600 ${labelSize}px ui-sans-serif, system-ui, sans-serif`
  ctx.fillText(n.label, cx, labelY)
  ctx.restore()
}

/** Draw a pin: lead-out stub + (if unconnected) small circle at the tip. */
function drawPin(
  ctx: CanvasRenderingContext2D,
  pin: EnumeratedPin,
  high: boolean, zoom: number, theme: Theme, connected: boolean,
  dark: boolean,
) {
  const { pos, innerPos } = pin
  // Lead-out stub: exactly 1·GRID long from the wall to the outer anchor.
  ctx.strokeStyle = connected ? (high ? theme.wireHigh : theme.wireLow)
    : (dark ? '#71717a' : '#94a3b8')
  ctx.lineWidth = connected
    ? clamp(2.0 / zoom, 1.2, 2.4)
    : clamp(1.5 / zoom, 1.0, 2.0)
  ctx.beginPath()
  ctx.moveTo(innerPos.x, innerPos.y)
  ctx.lineTo(pos.x, pos.y)
  ctx.stroke()

  if (!connected) {
    ctx.beginPath()
    ctx.arc(pos.x, pos.y, PIN_R, 0, Math.PI * 2)
    ctx.fillStyle = high ? theme.pinHigh : (dark ? '#52525b' : '#e2e8f0')
    ctx.fill()
    ctx.strokeStyle = high ? theme.pinHigh : theme.pinLow
    ctx.lineWidth = 1.3 / zoom
    ctx.stroke()
  } else {
    ctx.beginPath()
    ctx.arc(pos.x, pos.y, PIN_R * 0.55, 0, Math.PI * 2)
    ctx.fillStyle = high ? theme.pinHigh : (dark ? '#71717a' : '#94a3b8')
    ctx.fill()
  }
}

function strokeWirePath(ctx: CanvasRenderingContext2D, pts: Vec2[]) {
  if (pts.length < 2) return
  ctx.beginPath()
  ctx.moveTo(pts[0].x, pts[0].y)
  for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y)
}

function computeUnfoldedLayout(n: CircuitNode, chip: ChipDefinition) {
  const b = nodeBox(n)
  if (!chip.nodes.length) return null
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity
  for (const cn of chip.nodes) {
    const cb = nodeBox(cn)
    minX = Math.min(minX, cb.x); minY = Math.min(minY, cb.y)
    maxX = Math.max(maxX, cb.x + cb.w); maxY = Math.max(maxY, cb.y + cb.h)
  }
  const innerW = maxX - minX
  const innerH = maxY - minY
  const offX = b.x + (b.w - innerW) / 2 - minX
  const offY = b.y + 26 + (b.h - 26 - innerH) / 2 - minY
  const translated = chip.nodes.map((cn) => ({
    ...cn,
    position: { x: cn.position.x + offX, y: cn.position.y + offY },
  }))
  return { translated, offX, offY }
}

function drawUnfoldedChip(
  ctx: CanvasRenderingContext2D, n: CircuitNode, chip: ChipDefinition,
  selected: boolean, signal: SignalMap,
  chipMeta: Record<string, { color: string }>,
  zoom: number, theme: Theme, dark: boolean,
) {
  const b = nodeBox(n)
  const col = chip.color

  ctx.save()
  ctx.fillStyle = dark ? 'rgba(15,15,20,0.92)' : 'rgba(241,245,249,0.96)'
  roundRect(ctx, b.x, b.y, b.w, b.h, 4)
  ctx.fill()
  ctx.restore()

  if (selected) {
    ctx.save()
    ctx.strokeStyle = theme.sel
    ctx.lineWidth = 3 / zoom
    roundRect(ctx, b.x - 3, b.y - 3, b.w + 6, b.h + 6, 5)
    ctx.stroke()
    ctx.restore()
  }
  ctx.save()
  ctx.setLineDash([8 / zoom, 4 / zoom])
  ctx.strokeStyle = col
  ctx.lineWidth = 2 / zoom
  roundRect(ctx, b.x, b.y, b.w, b.h, 4)
  ctx.stroke()
  ctx.restore()

  ctx.save()
  ctx.beginPath()
  roundRect(ctx, b.x, b.y, b.w, 26, 4)
  ctx.clip()
  ctx.fillStyle = dark ? shade(col, -0.55) : shade(col, 0.85)
  ctx.fillRect(b.x, b.y, b.w, 26)
  ctx.restore()

  ctx.fillStyle = theme.label
  ctx.font = '700 11px ui-sans-serif, system-ui, sans-serif'
  ctx.textAlign = 'left'
  ctx.textBaseline = 'middle'
  ctx.fillText(`${chip.name.toUpperCase()} — UNFOLDED`, b.x + 12, b.y + 13)

  const btnW = 74, btnH = 18
  const bx = b.x + b.w - btnW - 8
  const by = b.y + 4
  ctx.fillStyle = dark ? '#334155' : '#ffffff'
  roundRect(ctx, bx, by, btnW, btnH, 3); ctx.fill()
  ctx.strokeStyle = col; ctx.lineWidth = 1 / zoom; ctx.stroke()
  ctx.fillStyle = theme.label
  ctx.font = '600 10px ui-sans-serif, system-ui, sans-serif'
  ctx.textAlign = 'center'
  ctx.fillText('Collapse', bx + btnW / 2, by + btnH / 2 + 0.5)

  const layout = computeUnfoldedLayout(n, chip)
  if (!layout) {
    ctx.fillStyle = theme.label
    ctx.font = '500 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'
    ctx.fillText('(empty)', b.x + b.w / 2, b.y + b.h / 2)
    return
  }
  const { translated } = layout

  for (const w of chip.wires) {
    const vw = wireView(w, translated, [])
    if (!vw) continue
    ctx.strokeStyle = theme.wireLow
    ctx.lineWidth = clamp(1.8 / zoom, 1, 2.4)
    strokeWirePath(ctx, vw.pts)
    ctx.stroke()
  }

  for (const cn of translated) {
    drawNode(ctx, cn, false, signal, chipMeta, zoom, theme, dark, 0.95)
  }
  for (const cn of translated) {
    for (const pin of enumeratePins(cn)) {
      drawPin(ctx, pin, !!signal[pinKey(pin.nodeId, pin.pinId)], zoom, theme, false, dark)
    }
  }
}

interface BridgeCrossing {
  point: Vec2
  overWireId: string
  underWireId: string
}

function computeBridgeCrossings(
  wirePolys: { w: Wire; pts: Vec2[] }[],
  junctions: Junction[],
): BridgeCrossing[] {
  const hasJunctionAt = (p: Vec2) => junctions.some((j) =>
    Math.abs(j.point.x - p.x) <= 0.5 && Math.abs(j.point.y - p.y) <= 0.5)
  const result: BridgeCrossing[] = []
  const seen = new Set<string>()

  const segments: { wireId: string; a: Vec2; b: Vec2 }[] = []
  for (const { w, pts } of wirePolys) {
    for (let i = 0; i < pts.length - 1; i++) {
      const a = pts[i], b = pts[i + 1]
      if (Math.abs(a.x - b.x) <= 0.5 || Math.abs(a.y - b.y) <= 0.5) {
        segments.push({ wireId: w.id, a, b })
      }
    }
  }

  for (const v of segments) {
    const vertical = Math.abs(v.a.x - v.b.x) <= 0.5 && Math.abs(v.a.y - v.b.y) > 0.5
    if (!vertical) continue
    const vx = v.a.x
    const vy0 = Math.min(v.a.y, v.b.y), vy1 = Math.max(v.a.y, v.b.y)

    for (const h of segments) {
      if (h.wireId === v.wireId) continue
      const horizontal = Math.abs(h.a.y - h.b.y) <= 0.5 && Math.abs(h.a.x - h.b.x) > 0.5
      if (!horizontal) continue
      const hy = h.a.y
      const hx0 = Math.min(h.a.x, h.b.x), hx1 = Math.max(h.a.x, h.b.x)
      if (vx < hx0 || vx > hx1 || hy < vy0 || hy > vy1) continue

      const point = { x: vx, y: hy }
      if (hasJunctionAt(point)) continue
      const key = `${v.wireId}:${h.wireId}:${vx}:${hy}`
      if (seen.has(key)) continue
      seen.add(key)
      result.push({ point, overWireId: v.wireId, underWireId: h.wireId })
    }
  }
  return result
}

function computeConnectedTerminals(wires: Wire[], junctions: Junction[]): Set<string> {
  const s = new Set<string>()
  for (const w of wires) {
    s.add(pinKey(w.from.nodeId, w.from.pinId))
    s.add(pinKey(w.to.nodeId, w.to.pinId))
  }
  for (const j of junctions) {
    s.add(pinKey(j.id, 'out'))
    s.add(pinKey(j.id, 'in'))
  }
  return s
}

function drawScene(
  ctx: CanvasRenderingContext2D, sw: number, sh: number, dpr: number,
  cam: Camera, nodes: CircuitNode[], wires: Wire[], junctions: Junction[], signal: SignalMap,
  selected: Set<string>, selectedWireId: string | null, selectedWireIds: Set<string>, hoverWireId: string | null,
  chipMeta: Record<string, { color: string }>,
  chipById: Record<string, ChipDefinition>,
  drawingPreview: { fromPos: Vec2; pts: Vec2[] } | null,
  bridgeCrossings: BridgeCrossing[],
  box: { x: number; y: number; w: number; h: number } | null,
  placingNode: CircuitNode | null,
  theme: Theme, dark: boolean,
) {
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0)
  ctx.clearRect(0, 0, sw, sh)
  ctx.fillStyle = theme.bg; ctx.fillRect(0, 0, sw, sh)

  const { zoom, offsetX, offsetY } = cam
  ctx.setTransform(dpr * zoom, 0, 0, dpr * zoom, dpr * offsetX, dpr * offsetY)

  const wl = -offsetX / zoom, wt = -offsetY / zoom
  const wr = (sw - offsetX) / zoom, wb = (sh - offsetY) / zoom
  drawGrid(ctx, wl, wt, wr, wb, zoom, theme.grid)

  const connectedTerminals = computeConnectedTerminals(wires, junctions)

  const wirePolys: { w: Wire; pts: Vec2[]; high: boolean; hover: boolean; isSel: boolean }[] = []
  for (const w of wires) {
    const vw = wireView(w, nodes, junctions)
    if (!vw) continue
    const high = !!signal[pinKey(w.from.nodeId, w.from.pinId)]
    wirePolys.push({
      w, pts: vw.pts, high,
      hover: hoverWireId === w.id,
      isSel: selectedWireId === w.id || selectedWireIds.has(w.id),
    })
  }
  type Seg = { wireId: string; a: Vec2; b: Vec2; high: boolean; hover: boolean; isSel: boolean }
  const segments: Seg[] = []
  for (const { w, pts, high, hover, isSel } of wirePolys) {
    for (let i = 0; i < pts.length - 1; i++) {
      segments.push({ wireId: w.id, a: pts[i], b: pts[i + 1], high, hover, isSel })
    }
  }

  const bridgeByWire = new Map<string, Vec2[]>()
  for (const bridge of bridgeCrossings) {
    const list = bridgeByWire.get(bridge.overWireId) ?? []
    list.push(bridge.point)
    bridgeByWire.set(bridge.overWireId, list)
  }

  const drawSegmentPieces = (seg: Seg, glow: boolean) => {
    const a = seg.a, b = seg.b
    const horizontal = Math.abs(a.y - b.y) <= 0.5
    const vertical = Math.abs(a.x - b.x) <= 0.5
    const crossings = (bridgeByWire.get(seg.wireId) ?? [])
      .filter((p) => horizontal
        ? Math.abs(p.y - a.y) <= 0.5 && p.x >= Math.min(a.x, b.x) && p.x <= Math.max(a.x, b.x)
        : vertical
          ? Math.abs(p.x - a.x) <= 0.5 && p.y >= Math.min(a.y, b.y) && p.y <= Math.max(a.y, b.y)
          : false)
      .sort((p, q) => horizontal ? p.x - q.x : p.y - q.y)

    const radius = 6 / zoom
    const lineWidth = glow ? 7 / zoom
      : seg.isSel ? clamp(3 / zoom, 1.6, 3.4)
        : clamp(2.1 / zoom, 1.2, 2.6)

    ctx.strokeStyle = glow ? theme.wireHigh + '30'
      : seg.isSel ? theme.sel : seg.hover ? theme.wireHover : seg.high ? theme.wireHigh : theme.wireLow
    ctx.lineWidth = lineWidth
    if (seg.hover || seg.isSel) ctx.setLineDash([5 / zoom, 3 / zoom])

    if (!crossings.length) {
      ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke()
      ctx.setLineDash([])
      return
    }

    let cursor = horizontal ? Math.min(a.x, b.x) : Math.min(a.y, b.y)
    const end = horizontal ? Math.max(a.x, b.x) : Math.max(a.y, b.y)
    const reverse = horizontal ? b.x < a.x : b.y < a.y

    const drawRange = (from: number, to: number) => {
      if (to - from <= 0.01) return
      const p0 = horizontal
        ? { x: reverse ? to : from, y: a.y }
        : { x: a.x, y: reverse ? to : from }
      const p1 = horizontal
        ? { x: reverse ? from : to, y: a.y }
        : { x: a.x, y: reverse ? from : to }
      ctx.beginPath(); ctx.moveTo(p0.x, p0.y); ctx.lineTo(p1.x, p1.y); ctx.stroke()
    }

    for (const crossing of crossings) {
      const at = horizontal ? crossing.x : crossing.y
      const gapStart = Math.max(cursor, at - radius)
      const gapEnd = Math.min(end, at + radius)
      drawRange(cursor, gapStart)
      cursor = Math.max(cursor, gapEnd)
    }
    drawRange(cursor, end)
    ctx.setLineDash([])
  }

  for (const seg of segments) {
    if (seg.high) drawSegmentPieces(seg, true)
    drawSegmentPieces(seg, false)
  }

  for (const bridge of bridgeCrossings) {
    const seg = segments.find((s) => s.wireId === bridge.overWireId
      && Math.abs(s.a.x - s.b.x) <= 0.5
      && bridge.point.x === s.a.x
      && bridge.point.y >= Math.min(s.a.y, s.b.y)
      && bridge.point.y <= Math.max(s.a.y, s.b.y))
    if (!seg) continue
    const { x, y } = bridge.point
    const r = 6 / zoom
    const color = seg.isSel ? theme.sel : seg.hover ? theme.wireHover : seg.high ? theme.wireHigh : theme.wireLow
    ctx.strokeStyle = color
    ctx.lineWidth = seg.isSel ? clamp(3 / zoom, 1.6, 3.4) : clamp(2.1 / zoom, 1.2, 2.6)
    if (seg.hover || seg.isSel) ctx.setLineDash([5 / zoom, 3 / zoom])
    ctx.beginPath()
    ctx.moveTo(x, y - r)
    ctx.bezierCurveTo(x + 2 * r, y - r * 0.65, x + 2 * r, y + r * 0.65, x, y + r)
    ctx.stroke()
    ctx.setLineDash([])
  }

  for (const n of nodes) {
    if (n.kind === 'CHIP' && n.unfolded && n.chipId && chipById[n.chipId]) {
      drawUnfoldedChip(ctx, n, chipById[n.chipId], selected.has(n.id), signal, chipMeta, zoom, theme, dark)
      continue
    }
    drawNode(ctx, n, selected.has(n.id), signal, chipMeta, zoom, theme, dark)
  }

  for (const n of nodes) {
    if (n.kind === 'CHIP' && n.unfolded && n.chipId && chipById[n.chipId]) continue
    for (const pin of enumeratePins(n)) {
      const connected = connectedTerminals.has(pinKey(pin.nodeId, pin.pinId))
      drawPin(ctx, pin, !!signal[pinKey(pin.nodeId, pin.pinId)], zoom, theme, connected, dark)
    }
  }

  if (drawingPreview && drawingPreview.pts.length >= 2) {
    ctx.strokeStyle = theme.wireHigh
    ctx.setLineDash([6 / zoom, 4 / zoom])
    ctx.lineWidth = 2 / zoom
    strokeWirePath(ctx, drawingPreview.pts)
    ctx.stroke()
    ctx.setLineDash([])
  }

  if (placingNode) {
    drawNode(ctx, placingNode, false, {}, chipMeta, zoom, theme, dark, 0.62)
    for (const pin of enumeratePins(placingNode))
      drawPin(ctx, pin, false, zoom, theme, false, dark)
  }

  if (box && (Math.abs(box.w) > 2 || Math.abs(box.h) > 2)) {
    const rx = Math.min(box.x, box.x + box.w), ry = Math.min(box.y, box.y + box.h)
    ctx.fillStyle = theme.sel + '14'; ctx.strokeStyle = theme.sel + '99'; ctx.lineWidth = 1 / zoom
    ctx.beginPath(); ctx.rect(rx, ry, Math.abs(box.w), Math.abs(box.h)); ctx.fill(); ctx.stroke()
  }
}

function renderNodesToImage(
  nodes: CircuitNode[], wires: Wire[], chipMeta: Record<string, { color: string }>,
  theme: Theme, dark: boolean, padding = 60, scale = 2,
): { dataUrl: string; width: number; height: number } {
  if (!nodes.length) {
    const w = 480, h = 240
    const canvas = document.createElement('canvas')
    canvas.width = w * scale; canvas.height = h * scale
    const ctx = canvas.getContext('2d')!
    ctx.setTransform(scale, 0, 0, scale, 0, 0)
    ctx.fillStyle = theme.bg; ctx.fillRect(0, 0, w, h)
    ctx.fillStyle = theme.label
    ctx.font = '600 16px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle'
    ctx.fillText('(empty)', w / 2, h / 2)
    return { dataUrl: canvas.toDataURL('image/png'), width: w, height: h }
  }
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity
  for (const n of nodes) {
    const b = nodeBox(n)
    minX = Math.min(minX, b.x); minY = Math.min(minY, b.y)
    maxX = Math.max(maxX, b.x + b.w); maxY = Math.max(maxY, b.y + b.h)
  }
  const w = (maxX - minX) + padding * 2
  const h = (maxY - minY) + padding * 2
  const canvas = document.createElement('canvas')
  canvas.width = Math.round(w * scale)
  canvas.height = Math.round(h * scale)
  const ctx = canvas.getContext('2d')!
  const cam: Camera = { zoom: 1, offsetX: -minX + padding, offsetY: -minY + padding }
  drawScene(
    ctx, w, h, scale, cam, nodes, wires, [], {}, new Set(), null, new Set(), null,
    chipMeta, {}, null, [], null, null, theme, dark,
  )
  return { dataUrl: canvas.toDataURL('image/png'), width: w, height: h }
}

/* Persistence */
const STORAGE_KEY = 'logicmaker.v8'
interface SavedState {
  nodes: CircuitNode[]; wires: Wire[]; junctions?: Junction[]
  chips: ChipDefinition[]; camera: Camera; dark?: boolean
}
function loadState(): Partial<SavedState> {
  try {
    const raw = localStorage.getItem(STORAGE_KEY)
    return raw ? JSON.parse(raw) : {}
  } catch { return {} }
}
function saveState(s: SavedState) {
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify({
      ...s,
      chips: s.chips.filter((c) => !c.builtin),
    }))
  } catch { /* */ }
}

/* Main */
type DragMode =
  | { kind: 'move'; ids: string[]; startWorld: Vec2; origin: Map<string, Vec2> }
  | { kind: 'box'; startX: number; startY: number; endX: number; endY: number }
  | null

export default function LogicSimulator() {
  const saved = useMemo(() => loadState(), [])
  const [nodes, setNodes] = useState<CircuitNode[]>(saved.nodes ?? [])
  const [wires, setWires] = useState<Wire[]>(saved.wires ?? [])
  const [junctions, setJunctions] = useState<Junction[]>(saved.junctions ?? [])
  const [chips, setChips] = useState<ChipDefinition[]>(() => [...makeBuiltInChips(), ...(saved.chips ?? [])])
  const [selected, setSelected] = useState<Set<string>>(new Set())
  const [selectedWireId, setSelectedWireId] = useState<string | null>(null)
  const [selectedWireIds, setSelectedWireIds] = useState<Set<string>>(new Set())
  const [placement, setPlacement] = useState<Placement>(null)
  const [camera, setCamera] = useState<Camera>(saved.camera ?? { zoom: 1, offsetX: 40, offsetY: 40 })
  const [editing, setEditing] = useState<EditSession | null>(null)
  const [createModal, setCreateModal] = useState(false)
  const [clockModal, setClockModal] = useState<{ id: string; period: number } | null>(null)
  const [renamePinModal, setRenamePinModal] = useState<{ nodeId: string; pinId: string; side: PinSide; name: string } | null>(null)
  const [changeBlockModal, setChangeBlockModal] = useState<{ nodeId: string } | null>(null)
  const [chipName, setChipName] = useState('My Chip')
  const [chipColor, setChipColor] = useState(CHIP_COLORS[0])
  const [customHex, setCustomHex] = useState('#2563eb')
  const [history, setHistory] = useState<HistoryEntry[]>([])
  const [redoStack, setRedoStack] = useState<HistoryEntry[]>([])
  const [clipboard, setClipboard] = useState<{ nodes: CircuitNode[]; wires: Wire[] } | null>(null)
  const [ctxMenu, setCtxMenu] = useState<ContextMenuState | null>(null)
  const [paletteCtxMenu, setPaletteCtxMenu] = useState<{ x: number; y: number; placement: Placement } | null>(null)
  const [dark, setDark] = useState(saved.dark ?? false)
  const [, setFrameTick] = useState(0)

  const theme = dark ? DARK : LIGHT
  const canvasRef = useRef<HTMLCanvasElement>(null)
  const drag = useRef<DragMode>(null)
  const pan = useRef<{ startScreenX: number; startScreenY: number; startOffsetX: number; startOffsetY: number } | null>(null)
  const spaceDown = useRef(false)
  const drawing = useRef<DrawSession | null>(null)
  const hoverWire = useRef<string | null>(null)
  const signal = useRef<SignalMap>({})
  const mousePos = useRef<Vec2>({ x: 0, y: 0 })
  const bridgeCrossings = useRef<BridgeCrossing[]>([])
  const hasLoaded = useRef(false)
  const modalOpen = useRef(false)
  const buttonHeld = useRef<string | null>(null)

  const live = useRef({ nodes, wires, junctions, chips, selected, selectedWireId, selectedWireIds, placement, camera })
  useEffect(() => {
    live.current = { nodes, wires, junctions, chips, selected, selectedWireId, selectedWireIds, placement, camera }
  })

  useEffect(() => {
    const wirePolys: { w: Wire; pts: Vec2[] }[] = []
    for (const w of wires) {
      const vw = wireView(w, nodes, junctions)
      if (vw) wirePolys.push({ w, pts: vw.pts })
    }
    bridgeCrossings.current = computeBridgeCrossings(wirePolys, junctions)
  }, [wires, nodes, junctions])

  useEffect(() => {
    modalOpen.current = !!(createModal || clockModal || renamePinModal || changeBlockModal)
  }, [createModal, clockModal, renamePinModal, changeBlockModal])

  const simulator = useMemo(() => new Simulator(), [])
  const chipsById = useMemo(() => Object.fromEntries(chips.map((c) => [c.id, c])), [chips])

  const netModel = useMemo(
    () => buildNetModel(nodes, wires, junctions, chipsById),
    [nodes, wires, junctions, chipsById],
  )

  useEffect(() => {
    simulator.load(netModel)
  }, [netModel, simulator])

  useEffect(() => {
    if (!hasLoaded.current) { hasLoaded.current = true; return }
    const t = setTimeout(() => saveState({ nodes, wires, junctions, chips, camera, dark }), 350)
    return () => clearTimeout(t)
  }, [nodes, wires, junctions, chips, camera, dark])

  useEffect(() => {
    let changed = false
    const next = junctions.map((j) => {
      const w = wires.find((x) => x.id === j.wireId)
      if (!w) return j
      const vw = wireView(w, nodes, junctions)
      if (!vw) return j
      let best = snapWirePoint(j.point), bestD = Infinity
      for (let i = 0; i < vw.pts.length - 1; i++) {
        const pr = projectOnSegment(j.point, vw.pts[i], vw.pts[i + 1])
        if (pr.dist < bestD) {
          bestD = pr.dist
          best = snapPointToSegment(j.point, vw.pts[i], vw.pts[i + 1])
        }
      }
      if (Math.hypot(best.x - j.point.x, best.y - j.point.y) > 0.5) {
        changed = true
        return { ...j, point: best }
      }
      return j
    })
    if (changed) setJunctions(next)
  }, [wires, nodes, junctions])

  useEffect(() => {
    const id = setInterval(() => {
      simulator.tick(live.current.nodes)
      signal.current = simulator.snapshot()
      setFrameTick((t) => (t + 1) % 1_000_000)
    }, 1000 / SIM_TPS)
    return () => clearInterval(id)
  }, [simulator])

  const snapshotCurrent = useCallback((): HistoryEntry => ({
    nodes: live.current.nodes.map((n) => ({
      ...n, position: { ...n.position },
      inputs: n.inputs.map((p) => ({ ...p })),
      outputs: n.outputs.map((p) => ({ ...p })),
      unfoldedPinPos: n.unfoldedPinPos
        ? { in: n.unfoldedPinPos.in.map((v) => ({ ...v })), out: n.unfoldedPinPos.out.map((v) => ({ ...v })) }
        : undefined,
    })),
    wires: live.current.wires.map((w) => ({
      ...w, from: { ...w.from }, to: { ...w.to },
      points: w.points?.map((m) => ({ ...m })),
    })),
    junctions: live.current.junctions.map((j) => ({ ...j, point: { ...j.point } })),
  }), [])

  const pushHistory = useCallback(() => {
    setHistory((h) => {
      const next = [...h, snapshotCurrent()]
      return next.length > 80 ? next.slice(-80) : next
    })
    setRedoStack([])
  }, [snapshotCurrent])

  const undo = useCallback(() => {
    setHistory((h) => {
      if (!h.length) return h
      const prev = h[h.length - 1]
      setRedoStack((r) => [...r, snapshotCurrent()].slice(-80))
      setNodes(prev.nodes); setWires(prev.wires); setJunctions(prev.junctions)
      setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set())
      return h.slice(0, -1)
    })
  }, [snapshotCurrent])

  const redo = useCallback(() => {
    setRedoStack((r) => {
      if (!r.length) return r
      const next = r[r.length - 1]
      setHistory((h) => [...h, snapshotCurrent()].slice(-80))
      setNodes(next.nodes); setWires(next.wires); setJunctions(next.junctions)
      setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set())
      return r.slice(0, -1)
    })
  }, [snapshotCurrent])

  const canvasRect = () => canvasRef.current!.getBoundingClientRect()
  const screenToWorld = (sx: number, sy: number): Vec2 => {
    const c = live.current.camera
    return { x: (sx - c.offsetX) / c.zoom, y: (sy - c.offsetY) / c.zoom }
  }
  const posFromEvent = (e: React.PointerEvent | React.MouseEvent) => {
    const r = canvasRect()
    return screenToWorld(e.clientX - r.left, e.clientY - r.top)
  }

  const findPinAt = (p: Vec2, extraGrab = 0) => {
    let best: EnumeratedPin | null = null, bestD = Infinity
    const grab = PIN_SNAP_RADIUS / live.current.camera.zoom + extraGrab
    for (const n of live.current.nodes)
      for (const pin of enumeratePins(n)) {
        const d = Math.hypot(p.x - pin.pos.x, p.y - pin.pos.y)
        if (d < grab && d < bestD) { bestD = d; best = pin }
      }
    return best
  }

  const isValidWireTarget = (pin: EnumeratedPin, from: PinRef) => {
    if (pin.nodeId === from.nodeId) return false
    if (from.side === 'out' && pin.side === 'in') return true
    if (from.side === 'in' && pin.side === 'out') return true
    return false
  }
  const findNodeAt = (p: Vec2) => {
    for (let i = live.current.nodes.length - 1; i >= 0; i--)
      if (hitNode(live.current.nodes[i], p)) return live.current.nodes[i]
    return null
  }
  const findHoveredWire = (p: Vec2) => {
    const zoom = live.current.camera.zoom
    let best: string | null = null, bestD = WIRE_SNAP_RADIUS / zoom
    for (const w of live.current.wires) {
      const vw = wireView(w, live.current.nodes, live.current.junctions)
      if (!vw) continue
      for (let i = 0; i < vw.pts.length - 1; i++) {
        const d = distToSegment(p, vw.pts[i], vw.pts[i + 1])
        if (d < bestD) { bestD = d; best = w.id }
      }
    }
    return best
  }
  const findCollapseButton = (p: Vec2, n: CircuitNode): boolean => {
    if (!n.unfolded) return false
    const b = nodeBox(n)
    const btnW = 74, btnH = 18
    const bx = b.x + b.w - btnW - 8
    const by = b.y + 4
    return p.x >= bx && p.x <= bx + btnW && p.y >= by && p.y <= by + btnH
  }

  const projectOnWire = (wireId: string, p: Vec2): Vec2 | null => {
    const w = live.current.wires.find((x) => x.id === wireId)
    if (!w) return null
    const vw = wireView(w, live.current.nodes, live.current.junctions)
    if (!vw) return null
    let best: Vec2 | null = null, bestD = Infinity
    for (let i = 0; i < vw.pts.length - 1; i++) {
      const pr = projectOnSegment(p, vw.pts[i], vw.pts[i + 1])
      if (pr.dist < bestD) {
        bestD = pr.dist
        best = snapPointToSegment(p, vw.pts[i], vw.pts[i + 1])
      }
    }
    return best
  }

  const place = (p: Vec2) => {
    if (!placement) return
    pushHistory()
    let node: CircuitNode
    if (placement.type === 'CHIP') {
      const chip = chipsById[placement.chipId]
      if (!chip) return
      node = createChipNode(chip, { x: 0, y: 0 })
    } else {
      node = createPrimitiveNode(placement.kind, { x: 0, y: 0 })
    }
    const w = nodeWidth(node)
    const h = nodeHeight(node)
    const snapped = { x: snap(p.x - w / 2), y: snap(p.y - h / 2) }
    node = { ...node, position: snapped }
    setNodes((ns) => [...ns, node])
    setSelected(new Set([node.id]))
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
    setPlacement(null)
  }

  const batchCreate = (placement: Placement, count: number) => {
    if (!placement) { setPaletteCtxMenu(null); return }
    pushHistory()
    const cursor = mousePos.current
    const sample = placement.type === 'PRIMITIVE'
      ? createPrimitiveNode(placement.kind, { x: 0, y: 0 })
      : (() => {
        const chip = chipsById[placement.chipId]
        return chip ? createChipNode(chip, { x: 0, y: 0 }) : null
      })()
    if (!sample) { setPaletteCtxMenu(null); return }
    const sampleW = nodeWidth(sample)
    const ghostH = nodeHeight(sample)
    const spacingY = snap(ghostH + 24)
    const newNodes: CircuitNode[] = []
    for (let i = 0; i < count; i++) {
      const pos = {
        x: snap(cursor.x - sampleW / 2),
        y: snap(cursor.y - ((count - 1) * spacingY) / 2 + i * spacingY - ghostH / 2),
      }
      let node: CircuitNode
      if (placement.type === 'CHIP') {
        const chip = chipsById[placement.chipId]
        if (!chip) continue
        node = createChipNode(chip, pos)
      } else {
        node = createPrimitiveNode(placement.kind, pos)
      }
      newNodes.push(node)
    }
    setNodes((ns) => [...ns, ...newNodes])
    setSelected(new Set(newNodes.map((n) => n.id)))
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
    setPaletteCtxMenu(null)
  }

  const startDrawing = (pin: EnumeratedPin) => {
    const start = snapWirePoint(pin.pos)
    drawing.current = {
      from: { nodeId: pin.nodeId, pinId: pin.pinId, side: pin.side },
      fromPos: start,
      points: [start],
      cursor: start,
      preferH: null,
    }
    mousePos.current = start
    setSelected(new Set())
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
  }

  const cancelDrawing = () => { drawing.current = null }

  const finishDrawing = (nodeId: string, pinId: string, side: PinSide, endPoint?: Vec2) => {
    const d = drawing.current
    if (!d) return
    let a = d.from
    let b: PinRef = { nodeId, pinId, side }
    if (a.side === 'in' && b.side === 'out') { const t = a; a = b; b = t }
    const toIsJunction = !!live.current.junctions.find((j) => j.id === b.nodeId)
    const fromIsJunction = !!live.current.junctions.find((j) => j.id === a.nodeId)
    if (!toIsJunction && !fromIsJunction) {
      if (a.side !== 'out' || b.side !== 'in' || a.nodeId === b.nodeId) { cancelDrawing(); return }
    } else if (a.nodeId === b.nodeId) {
      cancelDrawing()
      return
    }

    const targetPosRaw = endPoint ?? anchorOf(b.nodeId, b.pinId, b.side, live.current.nodes, live.current.junctions)
    if (!targetPosRaw) { cancelDrawing(); return }
    const targetPos = snapWirePoint(targetPosRaw)
    let points = addOrthogonalAnchor(d.points, targetPos, d.preferH)
    points[0] = { ...d.fromPos }
    points[points.length - 1] = { ...targetPos }
    points = collapsePolyline(points)

    pushHistory()
    setWires((ws) => [
      ...ws.filter((w) => !(w.to.side === 'in' && isPinRefEqual(w.to, b))),
      createWire(a, b, points),
    ])
    cancelDrawing()
  }

  const createJunctionOnWire = (wireId: string, p: Vec2): Junction | null => {
    const pt = projectOnWire(wireId, p)
    if (!pt) return null
    const j: Junction = { id: uid('j'), wireId, point: pt }
    setJunctions((js) => [...js, j])
    return j
  }

  const onPointerDown = (e: React.PointerEvent) => {
    setCtxMenu(null)
    setPaletteCtxMenu(null)
    canvasRef.current?.focus()
    const r = canvasRect()
    const sx = e.clientX - r.left, sy = e.clientY - r.top

    if (e.button === 1 || (e.button === 0 && spaceDown.current)) {
      e.preventDefault()
      canvasRef.current!.setPointerCapture(e.pointerId)
      pan.current = { startScreenX: sx, startScreenY: sy, startOffsetX: camera.offsetX, startOffsetY: camera.offsetY }
      canvasRef.current!.style.cursor = 'grabbing'
      return
    }
    if (e.button === 2) {
      if (drawing.current) { cancelDrawing(); return }
      return
    }

    const p = screenToWorld(sx, sy)
    canvasRef.current!.setPointerCapture(e.pointerId)

    if (placement) { place(p); return }

    if (drawing.current) {
      const d = drawing.current
      const pinHit = findPinAt(p, 8)
      if (pinHit && isValidWireTarget(pinHit, d.from)) {
        finishDrawing(pinHit.nodeId, pinHit.pinId, pinHit.side, pinHit.pos)
        return
      }
      const wireHitId = findHoveredWire(p)
      if (wireHitId) {
        const pt = projectOnWire(wireHitId, p)
        const j = pt ? createJunctionOnWire(wireHitId, pt) : null
        if (j) { finishDrawing(j.id, 'j', 'in', j.point); return }
      }
      // Commit current preview (collision-truncated) as the new fixed polyline.
      const raw = snapWirePoint(p)
      const preview = buildPreviewPolyline(d.points, raw, d.preferH, live.current.nodes, d.from.nodeId)
      d.points = [...d.points.slice(0, -1), ...preview]
      d.cursor = d.points[d.points.length - 1]
      d.preferH = null
      mousePos.current = d.cursor
      return
    }

    const node = findNodeAt(p)

    if (node && node.kind === 'CHIP' && node.unfolded && findCollapseButton(p, node)) {
      pushHistory()
      setNodes((ns) => ns.map((n) => n.id === node.id ? { ...n, unfolded: false, unfoldedSize: undefined, unfoldedPinPos: undefined } : n))
      return
    }

    if (node) {
      if (node.kind === 'INPUT' || node.kind === 'BUTTON' || node.kind === 'CLOCK') {
        const btnW = 48
        const btnH = Math.min(26, nodeHeight(node) - 6)
        const nw = nodeWidth(node)
        const bx = node.position.x + nw - btnW - 14
        const by = node.position.y + (nodeHeight(node) - btnH) / 2
        if (p.x >= bx && p.x <= bx + btnW && p.y >= by && p.y <= by + btnH) {
          if (node.kind === 'BUTTON') {
            buttonHeld.current = node.id
            setNodes((ns) => ns.map((n) => n.id === node.id ? { ...n, value: true } : n))
            setSelected(new Set([node.id]))
            setSelectedWireId(null); setSelectedWireIds(new Set())
            return
          }
          pushHistory()
          setNodes((ns) => ns.map((n) => n.id === node.id
            ? node.kind === 'CLOCK'
              ? { ...n, enabled: n.enabled === false ? true : false }
              : { ...n, value: !n.value }
            : n))
          setSelected(new Set([node.id]))
          setSelectedWireId(null); setSelectedWireIds(new Set())
          return
        }
      }
    }

    const pin = findPinAt(p)
    if (pin) { startDrawing(pin); return }

    if (node) {
      const multi = e.shiftKey || selected.has(node.id)
      const next = new Set<string>(multi ? selected : [])
      next.add(node.id)
      setSelected(next)
      setSelectedWireId(null)
      setSelectedWireIds(new Set())
      const origin = new Map<string, Vec2>()
      for (const n of live.current.nodes) if (next.has(n.id)) origin.set(n.id, { ...n.position })
      drag.current = { kind: 'move', ids: Array.from(next), startWorld: p, origin }
      return
    }

    const hw = findHoveredWire(p)
    if (hw) {
      const j = createJunctionOnWire(hw, p)
      if (j) {
        const pseudoPin: EnumeratedPin = {
          nodeId: j.id, pinId: 'out', side: 'out', index: 0,
          pos: j.point, innerPos: j.point,
          node: { id: j.id, kind: 'INPUT', label: '', position: j.point, inputs: [], outputs: [{ id: 'out', name: 'OUT' }] },
        }
        startDrawing(pseudoPin)
        return
      }
      setSelectedWireId(hw)
      setSelectedWireIds(new Set())
      setSelected(new Set())
      return
    }

    setSelected(new Set())
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
    drag.current = { kind: 'box', startX: p.x, startY: p.y, endX: p.x, endY: p.y }
  }

  const onPointerMove = (e: React.PointerEvent) => {
    const r = canvasRect()
    const sx = e.clientX - r.left, sy = e.clientY - r.top
    if (pan.current) {
      const p0 = pan.current
      setCamera((c) => ({
        ...c,
        offsetX: p0.startOffsetX + (sx - p0.startScreenX),
        offsetY: p0.startOffsetY + (sy - p0.startScreenY),
      }))
      return
    }
    const p = screenToWorld(sx, sy)
    mousePos.current = p

    if (drawing.current) {
      const d = drawing.current

      // Magnetise onto a valid target pin (cosmetic — the preview engine
      // will still enforce AABB collision).
      const magnetPin = findPinAt(p, 8)
      let raw: Vec2
      if (magnetPin && isValidWireTarget(magnetPin, d.from)) {
        raw = snapWirePoint(magnetPin.pos)
      } else {
        raw = snapWirePoint(p)
      }

      // Update first-segment orientation preference once, based on the
      // dominant axis of the very first movement.
      if (d.preferH === null) {
        const lastPt = d.points[d.points.length - 1]
        const adx = Math.abs(raw.x - lastPt.x)
        const ady = Math.abs(raw.y - lastPt.y)
        if (adx >= SUB_GRID || ady >= SUB_GRID) {
          d.preferH = adx >= ady
        }
      }

      d.cursor = raw
      mousePos.current = raw
      return
    }

    if (drag.current?.kind === 'box') { drag.current.endX = p.x; drag.current.endY = p.y }
    else if (drag.current?.kind === 'move') {
      const d = drag.current
      const dx = snap(p.x - d.startWorld.x), dy = snap(p.y - d.startWorld.y)
      const idSet = new Set(d.ids)
      const nextNodes = live.current.nodes.map((n) => idSet.has(n.id)
        ? { ...n, position: { x: d.origin.get(n.id)!.x + dx, y: d.origin.get(n.id)!.y + dy } }
        : n)
      live.current.nodes = nextNodes
      setNodes(nextNodes)
    } else {
      hoverWire.current = findHoveredWire(p)
    }
  }

  const onPointerUp = (e: React.PointerEvent) => {
    if (buttonHeld.current) {
      const id = buttonHeld.current
      buttonHeld.current = null
      setNodes((ns) => ns.map((n) => n.id === id ? { ...n, value: false } : n))
    }
    if (pan.current) {
      pan.current = null
      if (canvasRef.current) canvasRef.current.style.cursor = spaceDown.current ? 'grab' : 'default'
      return
    }
    if (drawing.current) {
      const r = canvasRect()
      const p = screenToWorld(e.clientX - r.left, e.clientY - r.top)
      const d = drawing.current
      const pinHit = findPinAt(p, 16)
      if (pinHit && isValidWireTarget(pinHit, d.from)) {
        finishDrawing(pinHit.nodeId, pinHit.pinId, pinHit.side, pinHit.pos)
      }
      return
    }

    const d = drag.current
    if (d?.kind === 'box') {
      const minX = Math.min(d.startX, d.endX), maxX = Math.max(d.startX, d.endX)
      const minY = Math.min(d.startY, d.endY), maxY = Math.max(d.startY, d.endY)
      const next = new Set<string>()
      for (const n of live.current.nodes) {
        const b = nodeBox(n)
        if (b.x < maxX && b.x + b.w > minX && b.y < maxY && b.y + b.h > minY) next.add(n.id)
      }
      setSelected(next)
      const wireIds = new Set<string>()
      for (const w of live.current.wires) {
        const vw = wireView(w, live.current.nodes, live.current.junctions)
        if (!vw) continue
        const inside = vw.pts.some((pt) => pt.x >= minX && pt.x <= maxX && pt.y >= minY && pt.y <= maxY)
        if (inside) wireIds.add(w.id)
      }
      setSelectedWireIds(wireIds)
      if (wireIds.size) setSelectedWireId(null)
    } else if (d?.kind === 'move') {
      const idSet = new Set(d.ids)
      setNodes((ns) => ns.map((n) => idSet.has(n.id)
        ? { ...n, position: { x: snap(n.position.x), y: snap(n.position.y) } } : n))
    }
    drag.current = null
  }

  const deleteSelection = () => {
    const boxWires = live.current.selectedWireIds
    const wireId = live.current.selectedWireId
    const ids = live.current.selected
    if (!boxWires.size && !wireId && !ids.size) return

    pushHistory()
    const wiresToDelete = new Set(boxWires)
    if (wireId) wiresToDelete.add(wireId)

    setNodes((ns) => ns.filter((n) => !ids.has(n.id)))
    setWires((ws) => ws.filter((w) => {
      if (wiresToDelete.has(w.id)) return false
      if (ids.has(w.from.nodeId) || ids.has(w.to.nodeId)) return false
      return true
    }))
    setJunctions((js) => js.filter((j) => !wiresToDelete.has(j.wireId) && !ids.has(j.wireId)))

    setSelected(new Set())
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
  }

  const copySelection = () => {
    const ids = live.current.selected
    if (!ids.size) return
    setClipboard({
      nodes: live.current.nodes.filter((n) => ids.has(n.id)).map((n) => ({
        ...n,
        position: { ...n.position },
        inputs: n.inputs.map((p) => ({ ...p })),
        outputs: n.outputs.map((p) => ({ ...p })),
      })),
      wires: live.current.wires
        .filter((w) => ids.has(w.from.nodeId) && ids.has(w.to.nodeId))
        .map((w) => ({
          ...w,
          from: { ...w.from },
          to: { ...w.to },
          points: w.points?.map((m) => ({ ...m })),
        })),
    })
  }
  const cutSelection = () => { copySelection(); deleteSelection() }
  const pasteClipboard = () => {
    const clip = clipboard
    if (!clip?.nodes.length) return
    pushHistory()
    const idMap = new Map<string, string>()
    const offset = 20
    const newNodes = clip.nodes.map((n) => {
      const newId = uid(n.kind.toLowerCase())
      idMap.set(n.id, newId)
      return {
        ...n,
        id: newId,
        position: { x: n.position.x + offset, y: n.position.y + offset },
        inputs: n.inputs.map((p) => ({ ...p })),
        outputs: n.outputs.map((p) => ({ ...p })),
        unfoldedPinPos: n.unfoldedPinPos
          ? { in: n.unfoldedPinPos.in.map((v) => ({ ...v })), out: n.unfoldedPinPos.out.map((v) => ({ ...v })) }
          : undefined,
      }
    })
    const newWires = clip.wires.map((w) => ({
      id: uid('w'),
      from: { ...w.from, nodeId: idMap.get(w.from.nodeId)! },
      to: { ...w.to, nodeId: idMap.get(w.to.nodeId)! },
      points: w.points?.map((m) => ({ x: m.x + offset, y: m.y + offset })),
    }))
    setNodes((ns) => [...ns, ...newNodes])
    setWires((ws) => [...ws, ...newWires])
    setSelected(new Set(newNodes.map((n) => n.id)))
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
  }

  const openCreateModal = () => {
    if (!selected.size) return
    setChipName('My Chip')
    setChipColor(CHIP_COLORS[0])
    setCustomHex('#2563eb')
    setCreateModal(true)
  }
  const confirmCreateChip = () => {
    const color = customHex || chipColor
    const def = packageSelectionInto(chipName.trim() || 'My Chip', color, live.current.nodes, live.current.wires, live.current.selected)
    if (!def) { window.alert('Need at least one INPUT/BUTTON/CLOCK and one OUTPUT.'); return }
    pushHistory()
    setChips((cs) => [...cs, def])
    const ids = new Set(def.nodes.map((n) => n.id))
    const instance = createChipNode(def, centroidOf(def.nodes))
    setNodes((ns) => [...ns.filter((n) => !ids.has(n.id)), instance])
    setWires((ws) => ws.filter((w) => !ids.has(w.from.nodeId) && !ids.has(w.to.nodeId)))
    setSelected(new Set([instance.id]))
    setCreateModal(false)
  }

  const unfoldChip = (nodeId: string) => {
    const node = live.current.nodes.find((n) => n.id === nodeId)
    if (!node || node.kind !== 'CHIP' || !node.chipId) return
    const chip = chipsById[node.chipId]
    if (!chip || !chip.nodes.length) return
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity
    for (const cn of chip.nodes) {
      const b = nodeBox(cn)
      minX = Math.min(minX, b.x); minY = Math.min(minY, b.y)
      maxX = Math.max(maxX, b.x + b.w); maxY = Math.max(maxY, b.y + b.h)
    }
    const pad = 40, header = 28
    const w = snap(Math.max(260, (maxX - minX) + pad * 2))
    const h = snap(Math.max(140, (maxY - minY) + pad * 2 + header))

    const offX = node.position.x + (w - (maxX - minX)) / 2 - minX
    const offY = node.position.y + header + (h - header - (maxY - minY)) / 2 - minY
    const byId = new Map<string, CircuitNode>(chip.nodes.map((cn) => [cn.id, {
      ...cn,
      position: { x: cn.position.x + offX, y: cn.position.y + offY },
    } as CircuitNode]))

    const inPins: Vec2[] = chip.inputNodeIds.map((id) => {
      const cn = byId.get(id)
      const p = cn ? rightPinPos(cn, 0) : { x: node.position.x, y: node.position.y }
      return { x: p.x - node.position.x, y: p.y - node.position.y }
    })
    const outPins: Vec2[] = chip.outputNodeIds.map((id) => {
      const cn = byId.get(id)
      const p = cn ? leftPinPos(cn, 0) : { x: node.position.x + w, y: node.position.y }
      return { x: p.x - node.position.x, y: p.y - node.position.y }
    })

    pushHistory()
    setNodes((ns) => ns.map((n) => n.id === nodeId
      ? { ...n, unfolded: true, unfoldedSize: { w, h }, unfoldedPinPos: { in: inPins, out: outPins } }
      : n))
  }
  const foldChip = (nodeId: string) => {
    pushHistory()
    setNodes((ns) => ns.map((n) => n.id === nodeId
      ? { ...n, unfolded: false, unfoldedSize: undefined, unfoldedPinPos: undefined }
      : n))
  }

  const enterEditChip = (chipId: string) => {
    if (editing) return
    const chip = chipsById[chipId]
    if (!chip || chip.builtin) return
    setCtxMenu(null)
    setEditing({
      chipId,
      snapNodes: live.current.nodes,
      snapWires: live.current.wires,
      snapJunctions: live.current.junctions,
      snapSelected: live.current.selected,
      snapCamera: live.current.camera,
    })
    const mapped = chip.nodes.map((n) => ({ ...n, position: { ...n.position } }))
    setNodes(mapped)
    setWires(chip.wires.map((w) => ({ ...w })))
    setJunctions([])
    setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setPlacement(null)
    drawing.current = null
    if (mapped.length) {
      let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity
      for (const n of mapped) {
        const b = nodeBox(n)
        minX = Math.min(minX, b.x); minY = Math.min(minY, b.y)
        maxX = Math.max(maxX, b.x + b.w); maxY = Math.max(maxY, b.y + b.h)
      }
      const cx = (minX + maxX) / 2, cy = (minY + maxY) / 2
      const canvas = canvasRef.current
      const cw = canvas?.clientWidth ?? 800, ch = canvas?.clientHeight ?? 600
      setCamera({ zoom: 1, offsetX: cw / 2 - cx, offsetY: ch / 2 - cy })
    } else {
      setCamera({ zoom: 1, offsetX: 40, offsetY: 40 })
    }
  }

  const centerView = () => {
    const ns = live.current.nodes
    if (!ns.length) {
      setCamera({ zoom: 1, offsetX: 40, offsetY: 40 })
      return
    }
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity
    for (const n of ns) {
      const b = nodeBox(n)
      minX = Math.min(minX, b.x); minY = Math.min(minY, b.y)
      maxX = Math.max(maxX, b.x + b.w); maxY = Math.max(maxY, b.y + b.h)
    }
    const cx = (minX + maxX) / 2, cy = (minY + maxY) / 2
    const canvas = canvasRef.current
    const cw = canvas?.clientWidth ?? 800, ch = canvas?.clientHeight ?? 600
    const pad = 80
    const contentW = maxX - minX + pad * 2
    const contentH = maxY - minY + pad * 2
    const zoom = clamp(Math.min(cw / contentW, ch / contentH, 1.5), MIN_ZOOM, MAX_ZOOM)
    setCamera({ zoom, offsetX: cw / 2 - cx * zoom, offsetY: ch / 2 - cy * zoom })
  }

  const exitEditChip = (save: boolean) => {
    setEditing((session) => {
      if (!session) return null
      if (save) {
        const curNodes = live.current.nodes, curWires = live.current.wires
        const inputs = curNodes.filter((n) => n.kind === 'INPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK')
          .sort((a, b) => a.position.y - b.position.y)
        const outputs = curNodes.filter((n) => n.kind === 'OUTPUT').sort((a, b) => a.position.y - b.position.y)
        if (!inputs.length || !outputs.length) {
          window.alert('Need at least one INPUT and one OUTPUT.'); return session
        }
        const chip = chipsById[session.chipId]
        const updated: ChipDefinition = {
          ...chip, nodes: curNodes, wires: curWires,
          inputNodeIds: inputs.map((n) => n.id), outputNodeIds: outputs.map((n) => n.id),
        }
        setChips((cs) => cs.map((c) => c.id === session.chipId ? updated : c))
        const validIn = new Set(updated.inputNodeIds.map((_, i) => `i${i}`))
        const validOut = new Set(updated.outputNodeIds.map((_, i) => `o${i}`))
        const refreshed = session.snapNodes.map((n) =>
          n.kind === 'CHIP' && n.chipId === session.chipId ? refreshChipInstance(n, updated) : n)
        const refreshedIds = new Set(refreshed.filter((n) => n.chipId === session.chipId).map((n) => n.id))
        setNodes(refreshed)
        setWires(session.snapWires.filter((w) => {
          const fromStale = refreshedIds.has(w.from.nodeId) && !validOut.has(w.from.pinId)
          const toStale = refreshedIds.has(w.to.nodeId) && !validIn.has(w.to.pinId)
          return !fromStale && !toStale
        }))
        setJunctions(session.snapJunctions)
      } else {
        setNodes(session.snapNodes); setWires(session.snapWires); setJunctions(session.snapJunctions)
      }
      setSelected(session.snapSelected); setSelectedWireId(null); setSelectedWireIds(new Set()); setCamera(session.snapCamera)
      setPlacement(null); drawing.current = null
      return null
    })
  }

  const renameChipInEdit = (name: string) => {
    if (!editing) return
    setChips((cs) => cs.map((c) => c.id === editing.chipId ? { ...c, name } : c))
  }

  const applyPinRename = () => {
    if (!renamePinModal) return
    const { nodeId, pinId, side, name } = renamePinModal
    setNodes((ns) => ns.map((n) => {
      if (n.id !== nodeId) return n
      if (side === 'in') {
        return { ...n, inputs: n.inputs.map((p) => p.id === pinId ? { ...p, name: name.trim() || p.name } : p) }
      }
      return { ...n, outputs: n.outputs.map((p) => p.id === pinId ? { ...p, name: name.trim() || p.name } : p) }
    }))
    setNodes((ns) => ns.map((n) => {
      if (n.id !== nodeId) return n
      if ((n.kind === 'INPUT' || n.kind === 'OUTPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK') && side === (n.kind === 'OUTPUT' ? 'in' : 'out')) {
        return { ...n, label: name.trim() || n.label }
      }
      return n
    }))
    setRenamePinModal(null)
  }

  const applyNodeReplacement = (
    nodeId: string,
    target: { type: 'PRIMITIVE'; kind: PrimitiveType } | { type: 'CHIP'; chipId: string },
  ) => {
    pushHistory()
    const old = live.current.nodes.find((n) => n.id === nodeId)
    if (!old) return

    let newInputs: Pin[]
    let newOutputs: Pin[]
    let newLabel: string
    let newKind: NodeKind
    let chipId: string | undefined
    let value: boolean | undefined
    let period: number | undefined
    let enabled: boolean | undefined

    if (target.type === 'PRIMITIVE') {
      const spec = PRIMITIVE_SPEC[target.kind]
      newInputs = makePins(spec.inputs)
      newOutputs = makePins(spec.outputs)
      newLabel = spec.label
      newKind = target.kind
      value = (target.kind === 'INPUT' || target.kind === 'BUTTON') ? (old.value ?? false) : undefined
      period = target.kind === 'CLOCK' ? (old.period ?? 30) : undefined
      enabled = target.kind === 'CLOCK' ? (old.enabled ?? true) : undefined
    } else {
      const chip = chipsById[target.chipId]
      if (!chip) return
      newInputs = chip.inputNodeIds.map((nid, i) => ({
        id: `i${i}`,
        name: labelOfNode(chip.nodes, nid) || `IN${i}`,
      }))
      newOutputs = chip.outputNodeIds.map((nid, i) => ({
        id: `o${i}`,
        name: labelOfNode(chip.nodes, nid) || `OUT${i}`,
      }))
      newLabel = chip.name
      newKind = 'CHIP'
      chipId = chip.id
    }

    const inMap = new Map<string, string>()
    old.inputs.forEach((p, i) => { if (i < newInputs.length) inMap.set(p.id, newInputs[i].id) })
    const outMap = new Map<string, string>()
    old.outputs.forEach((p, i) => { if (i < newOutputs.length) outMap.set(p.id, newOutputs[i].id) })

    setNodes((ns) => ns.map((n) => {
      if (n.id !== nodeId) return n
      return {
        ...n,
        kind: newKind,
        chipId,
        label: newLabel,
        inputs: newInputs,
        outputs: newOutputs,
        value,
        period,
        enabled,
        unfolded: false,
        unfoldedSize: undefined,
        unfoldedPinPos: undefined,
      }
    }))

    setWires((ws) => ws.flatMap((w) => {
      let from = { ...w.from }
      let to = { ...w.to }
      let keep = true
      if (from.nodeId === nodeId) {
        const mapped = outMap.get(from.pinId)
        if (mapped) from = { ...from, pinId: mapped }
        else keep = false
      }
      if (to.nodeId === nodeId) {
        const mapped = inMap.get(to.pinId)
        if (mapped) to = { ...to, pinId: mapped }
        else keep = false
      }
      if (!keep) return []
      return [{ ...w, from, to }]
    }))
    setChangeBlockModal(null)
  }

  const rotateNode = (nodeId: string, delta: 90 | 180 | 270) => {
    pushHistory()
    setNodes((ns) => ns.map((n) => n.id === nodeId
      ? { ...n, rotation: ((((n.rotation || 0) + delta) % 360) as 0 | 90 | 180 | 270) }
      : n))
  }

  const onDoubleClick = (e: React.MouseEvent) => {
    if (drawing.current) { cancelDrawing(); return }
    if (placement) return
    const p = screenToWorld(e.clientX - canvasRect().left, e.clientY - canvasRect().top)
    const pin = findPinAt(p)
    if (pin) {
      const n = pin.node
      if (n.kind === 'INPUT' || n.kind === 'OUTPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK') {
        const side = n.kind === 'OUTPUT' ? 'in' : 'out'
        const pinList = side === 'in' ? n.inputs : n.outputs
        const thePin = pinList.find((x) => x.id === pin.pinId) ?? pinList[0]
        setRenamePinModal({
          nodeId: n.id,
          pinId: thePin?.id ?? pin.pinId,
          side,
          name: n.label,
        })
      }
      return
    }
    if (editing) return
    const node = findNodeAt(p)
    if (node?.kind === 'CLOCK') {
      setClockModal({ id: node.id, period: node.period ?? 30 })
      setSelected(new Set([node.id]))
      setSelectedWireId(null); setSelectedWireIds(new Set())
      return
    }
    if (node?.kind === 'CHIP' && node.chipId) {
      if (!chipsById[node.chipId]?.builtin) {
        if (node.unfolded) foldChip(node.id)
        else unfoldChip(node.id)
      }
    }
  }

  const onContextMenu = (e: React.MouseEvent) => {
    e.preventDefault()
    if (drawing.current) { cancelDrawing(); return }
    const p = posFromEvent(e)
    const node = findNodeAt(p)
    const wireId = findHoveredWire(p)
    let target: ContextMenuState['target'] = 'canvas'
    let nodeId: string | undefined, wId: string | undefined

    if (node) {
      if (node.kind === 'CHIP' && node.chipId && !chipsById[node.chipId]?.builtin) {
        target = node.unfolded ? 'unfoldedChip' : 'chip'
      } else {
        target = 'node'
      }
      nodeId = node.id
      if (!selected.has(node.id)) setSelected(new Set([node.id]))
      setSelectedWireId(null)
      setSelectedWireIds(new Set())
    } else if (wireId) {
      target = 'wire'; wId = wireId
      setSelectedWireId(wireId); setSelected(new Set()); setSelectedWireIds(new Set())
    }
    setCtxMenu({ x: e.clientX, y: e.clientY, world: p, target, nodeId, wireId: wId })
  }

  const ctxAction = (action: string) => {
    if (!ctxMenu) return
    const wireId = ctxMenu.wireId
    const nodeId = ctxMenu.nodeId
    setCtxMenu(null)
    if (action === 'cut') cutSelection()
    else if (action === 'copy') copySelection()
    else if (action === 'paste') pasteClipboard()
    else if (action === 'delete') {
      if (wireId && ctxMenu.target === 'wire') {
        pushHistory()
        setWires((ws) => ws.filter((w) => w.id !== wireId))
        setJunctions((js) => js.filter((j) => j.wireId !== wireId))
        setSelectedWireId(null)
      } else {
        deleteSelection()
      }
    } else if (action === 'edit' && nodeId) {
      const n = nodes.find((x) => x.id === nodeId)
      if (n?.chipId) enterEditChip(n.chipId)
    } else if (action === 'changeBlock' && nodeId) {
      setChangeBlockModal({ nodeId })
    } else if (action === 'unfold' && nodeId) {
      unfoldChip(nodeId)
    } else if (action === 'fold' && nodeId) {
      foldChip(nodeId)
    } else if (action === 'rotate90' && nodeId) {
      rotateNode(nodeId, 90)
    } else if (action === 'rotate180' && nodeId) {
      rotateNode(nodeId, 180)
    } else if (action === 'rotate270' && nodeId) {
      rotateNode(nodeId, 270)
    } else if (action === 'toggleClock' && nodeId) {
      pushHistory()
      setNodes((ns) => ns.map((n) => n.id === nodeId ? { ...n, enabled: n.enabled === false ? true : false } : n))
    } else if (action === 'clockSettings' && nodeId) {
      const n = nodes.find((x) => x.id === nodeId)
      if (n) setClockModal({ id: nodeId, period: n.period ?? 30 })
    } else if (action === 'rename' && nodeId) {
      const n = nodes.find((x) => x.id === nodeId)
      if (!n) return
      if (n.kind === 'INPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK') {
        setRenamePinModal({ nodeId: n.id, pinId: n.outputs[0]?.id ?? 'out', side: 'out', name: n.label })
      } else if (n.kind === 'OUTPUT') {
        setRenamePinModal({ nodeId: n.id, pinId: n.inputs[0]?.id ?? 'in', side: 'in', name: n.label })
      }
    }
  }

  const clearAll = () => {
    if (editing) return
    pushHistory()
    setNodes([]); setWires([]); setJunctions([]); setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setPlacement(null)
    drawing.current = null
    simulator.reset(); signal.current = {}
  }

  const exportJSON = () => {
    const model = buildNetModel(nodes, wires, junctions, chipsById)
    const adjacency: Record<string, string[]> = {}
    for (const [key, root] of model.terminalNet) {
      if (!adjacency[root]) adjacency[root] = []
      adjacency[root].push(key)
    }
    const data = {
      version: 8,
      nodes,
      wires,
      junctions,
      chips: chips.filter((c) => !c.builtin),
      camera,
      dark,
      netAdjacency: adjacency,
    }
    const blob = new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a'); a.href = url; a.download = `LogicMaker_${Date.now()}.json`; a.click()
    URL.revokeObjectURL(url)
  }
  const importJSON = () => {
    const input = document.createElement('input'); input.type = 'file'; input.accept = '.json'
    input.onchange = async () => {
      const file = input.files?.[0]; if (!file) return
      try {
        const data = JSON.parse(await file.text())
        if (!Array.isArray(data.nodes) || !Array.isArray(data.wires)) throw new Error()
        pushHistory()
        setNodes(data.nodes); setWires(data.wires); setJunctions(data.junctions ?? [])
        setChips([...makeBuiltInChips(), ...(data.chips ?? [])])
        if (data.camera) setCamera(data.camera)
        if (typeof data.dark === 'boolean') setDark(data.dark)
        setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setPlacement(null); drawing.current = null
      } catch { window.alert('Invalid file') }
    }
    input.click()
  }

  const exportPDF = async () => {
    let jsPDFCtor: any
    try {
      const mod: any = await import('jspdf')
      jsPDFCtor = mod.jsPDF ?? mod.default
    } catch {
      window.alert('PDF export requires the "jspdf" package. Install it with: npm install jspdf')
      return
    }
    const chipMetaAll: Record<string, { color: string }> = {}
    for (const c of chips) chipMetaAll[c.id] = { color: c.color }

    const doc = new jsPDFCtor({ orientation: 'landscape', unit: 'px', format: 'a4' })
    const pageW = doc.internal.pageSize.getWidth()
    const pageH = doc.internal.pageSize.getHeight()

    const addImagePage = (title: string, img: { dataUrl: string; width: number; height: number }, first: boolean) => {
      if (!first) doc.addPage()
      doc.setFontSize(16)
      doc.text(title, 24, 28)
      const maxW = pageW - 48, maxH = pageH - 64
      const ratio = Math.min(maxW / img.width, maxH / img.height, 1)
      const w = img.width * ratio, h = img.height * ratio
      doc.addImage(img.dataUrl, 'PNG', 24, 48, w, h)
    }

    addImagePage('Main Schematic', renderNodesToImage(nodes, wires, chipMetaAll, LIGHT, false), true)
    for (const chip of chips.filter((c) => !c.builtin)) {
      addImagePage(`Chip: ${chip.name} (unfolded)`, renderNodesToImage(chip.nodes, chip.wires, chipMetaAll, LIGHT, false), false)
    }
    const ts = new Date().toISOString().replace(/[:.]/g, '-').replace('T', '_').slice(0, 19)
    doc.save(`Logic_Schematic_Export_${ts}.pdf`)
  }

  const actionsRef = useRef({
    undo, redo, copySelection, cutSelection, pasteClipboard, deleteSelection,
  })
  useEffect(() => {
    actionsRef.current = { undo, redo, copySelection, cutSelection, pasteClipboard, deleteSelection }
  })

  useEffect(() => {
    const down = (e: KeyboardEvent) => {
      const tag = (e.target as HTMLElement)?.tagName
      if (modalOpen.current || tag === 'INPUT' || tag === 'TEXTAREA') return
      if (e.code === 'Space') {
        if (!spaceDown.current) {
          spaceDown.current = true
          if (canvasRef.current && !pan.current) canvasRef.current.style.cursor = 'grab'
        }
        e.preventDefault(); return
      }
      const mod = e.ctrlKey || e.metaKey
      if (mod && e.code === 'KeyZ' && !e.shiftKey) { e.preventDefault(); actionsRef.current.undo(); return }
      if (mod && (e.code === 'KeyY' || (e.code === 'KeyZ' && e.shiftKey))) { e.preventDefault(); actionsRef.current.redo(); return }
      if (mod && e.code === 'KeyC') { e.preventDefault(); actionsRef.current.copySelection(); return }
      if (mod && e.code === 'KeyV') { e.preventDefault(); actionsRef.current.pasteClipboard(); return }
      if (mod && e.code === 'KeyX') { e.preventDefault(); actionsRef.current.cutSelection(); return }
      if (e.key === 'Escape') {
        drawing.current = null
        setPlacement(null); setCreateModal(false)
        setClockModal(null); setRenamePinModal(null); setChangeBlockModal(null); setCtxMenu(null); setPaletteCtxMenu(null)
        setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set())
      }
      if ((e.key === 'Delete' || e.key === 'Backspace')
        && (live.current.selected.size > 0
          || live.current.selectedWireId
          || live.current.selectedWireIds.size > 0)) {
        e.preventDefault()
        actionsRef.current.deleteSelection()
      }
    }
    const up = (e: KeyboardEvent) => {
      if (e.code === 'Space') {
        spaceDown.current = false
        if (canvasRef.current && !pan.current) canvasRef.current.style.cursor = 'default'
      }
    }
    window.addEventListener('keydown', down, true)
    window.addEventListener('keyup', up, true)
    return () => {
      window.removeEventListener('keydown', down, true)
      window.removeEventListener('keyup', up, true)
    }
  }, [])

  useEffect(() => {
    const canvas = canvasRef.current
    if (!canvas) return
    const onWheel = (e: WheelEvent) => {
      e.preventDefault()
      const r = canvas.getBoundingClientRect()
      const sx = e.clientX - r.left, sy = e.clientY - r.top
      setCamera((cam) => {
        const factor = Math.exp(-e.deltaY * 0.0011)
        const newZoom = clamp(cam.zoom * factor, MIN_ZOOM, MAX_ZOOM)
        const wx = (sx - cam.offsetX) / cam.zoom, wy = (sy - cam.offsetY) / cam.zoom
        return { zoom: newZoom, offsetX: sx - wx * newZoom, offsetY: sy - wy * newZoom }
      })
    }
    canvas.addEventListener('wheel', onWheel, { passive: false })
    return () => canvas.removeEventListener('wheel', onWheel)
  }, [])

  useEffect(() => {
    let raf = 0
    const loop = () => {
      raf = requestAnimationFrame(loop)
      const canvas = canvasRef.current
      if (!canvas) return
      const dpr = window.devicePixelRatio || 1
      const ctx = canvas.getContext('2d')
      if (!ctx) return
      const cw = canvas.clientWidth, ch = canvas.clientHeight
      if (canvas.width !== Math.round(cw * dpr) || canvas.height !== Math.round(ch * dpr)) {
        canvas.width = Math.round(cw * dpr); canvas.height = Math.round(ch * dpr)
      }
      const s = live.current
      const box = drag.current?.kind === 'box'
        ? { x: drag.current.startX, y: drag.current.startY, w: drag.current.endX - drag.current.startX, h: drag.current.endY - drag.current.startY }
        : null

      // ---- SEGMENT-BASED CORRIDOR PREVIEW -------------------------
      // The preview is built by first picking the raw L-shape from the
      // last committed point to the current mouse position, then running
      // a segment-by-segment AABB test.  If NEITHER dynamic segment hits
      // a component, the L-shape is rendered whole → the wire is
      // UNFROZEN.  Otherwise it truncates at the entry boundary.
      let drawingPreview: { fromPos: Vec2; pts: Vec2[] } | null = null
      if (drawing.current) {
        const d = drawing.current
        const preview = buildPreviewPolyline(
          d.points,
          mousePos.current,
          d.preferH,
          s.nodes,
          d.from.nodeId,
        )
        // Stitch: everything except the last committed point, then the
        // freshly computed preview segments.
        const fullPath = [...d.points.slice(0, -1), ...preview]
        drawingPreview = { fromPos: d.fromPos, pts: fullPath }
      }

      const chipMeta: Record<string, { color: string }> = {}
      for (const c of s.chips) chipMeta[c.id] = { color: c.color }
      const chipById: Record<string, ChipDefinition> = {}
      for (const c of s.chips) chipById[c.id] = c

      let placingNode: CircuitNode | null = null
      if (s.placement) {
        if (s.placement.type === 'CHIP') {
          const chip = s.chips.find((c) => c.id === s.placement!.chipId)
          if (chip) {
            const temp = createChipNode(chip, { x: 0, y: 0 })
            const w = nodeWidth(temp)
            const h = nodeHeight(temp)
            placingNode = createChipNode(chip, {
              x: snap(mousePos.current.x - w / 2),
              y: snap(mousePos.current.y - h / 2),
            })
          }
        } else {
          const temp = createPrimitiveNode(s.placement.kind, { x: 0, y: 0 })
          const w = nodeWidth(temp)
          const h = nodeHeight(temp)
          placingNode = createPrimitiveNode(s.placement.kind, {
            x: snap(mousePos.current.x - w / 2),
            y: snap(mousePos.current.y - h / 2),
          })
        }
      }

      drawScene(ctx, cw, ch, dpr, s.camera, s.nodes, s.wires, s.junctions, signal.current,
        s.selected, s.selectedWireId, s.selectedWireIds, hoverWire.current,
        chipMeta, chipById, drawingPreview, bridgeCrossings.current, box, placingNode, theme, dark)
    }
    loop()
    return () => cancelAnimationFrame(raf)
  }, [theme, dark])

  const btn = 'inline-flex flex-col items-center justify-center gap-0.5 rounded-md px-2.5 py-1.5 text-[11px] font-medium transition select-none'
  const active = dark ? 'bg-sky-900/50 text-sky-300 ring-1 ring-sky-500/50' : 'bg-blue-100 text-blue-700 ring-1 ring-blue-400/60'
  const idle = dark ? 'text-slate-300 hover:bg-slate-700' : 'text-slate-600 hover:bg-slate-100 hover:text-slate-900'
  const isPrim = (k: PrimitiveType) => placement?.type === 'PRIMITIVE' && placement.kind === k
  const isChip = (id: string) => placement?.type === 'CHIP' && placement.chipId === id
  const builtinChips = chips.filter((c) => c.builtin)
  const customChips = chips.filter((c) => !c.builtin)
  const editingChip = editing ? chipsById[editing.chipId] : null
  const menuItemCls = `flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`

  const clampMenuPos = (clientX: number, clientY: number, estimatedW: number, estimatedH: number) => {
    const pad = 8
    let left = clientX
    let top = clientY
    if (left + estimatedW > window.innerWidth - pad) left = Math.max(pad, clientX - estimatedW)
    if (top + estimatedH > window.innerHeight - pad) top = Math.max(pad, clientY - estimatedH)
    return { left, top }
  }

  return (
    <div className={`flex h-screen w-screen flex-col overflow-hidden ${dark ? 'bg-slate-900 text-slate-100' : 'bg-slate-100 text-slate-800'}`}>
      <header className={`flex h-11 shrink-0 items-center gap-2 border-b px-3 shadow-sm ${dark ? 'border-slate-700 bg-slate-800' : 'border-slate-200 bg-white'}`}>
        <span className="text-sm font-bold tracking-tight">
          Logic<span className="text-blue-500">Maker</span>
        </span>

        {editingChip ? (
          <div className="flex flex-1 items-center gap-2">
            <input
              value={editingChip.name}
              onChange={(e) => renameChipInEdit(e.target.value)}
              className={`rounded border px-2 py-0.5 text-xs font-semibold outline-none ${dark ? 'border-slate-600 bg-slate-900' : 'border-slate-200 bg-slate-50'}`}
              style={{ color: editingChip.color }}
            />
            <span className="text-[11px] opacity-50">Edit mode — double-click pins to rename</span>
            <div className="flex-1" />
            <button onClick={() => exitEditChip(false)} className={`${btn} ${idle}`}>Cancel</button>
            <button onClick={() => exitEditChip(true)} className={`${btn} bg-emerald-50 text-emerald-700`}>Save & Close</button>
          </div>
        ) : (
          <>
            <button onClick={openCreateModal} disabled={!selected.size}
              className={`${btn} ${!selected.size ? 'cursor-not-allowed opacity-40' : 'bg-emerald-50 text-emerald-700 hover:bg-emerald-100'}`}>
              Create Chip
            </button>
            <div className={`mx-1 h-5 w-px ${dark ? 'bg-slate-600' : 'bg-slate-200'}`} />
            <button onClick={undo} className={`${btn} ${idle}`} title="Undo (Ctrl+Z)" disabled={history.length === 0}>
              <RotateCcw size={14} />
              <span className="text-[10px]">Undo</span>
            </button>
            <button onClick={redo} className={`${btn} ${idle}`} title="Redo (Ctrl+Y)" disabled={redoStack.length === 0}>
              <RotateCw size={14} />
              <span className="text-[10px]">Redo</span>
            </button>
            <div className={`mx-1 h-5 w-px ${dark ? 'bg-slate-600' : 'bg-slate-200'}`} />
            <button onClick={exportJSON} className={`${btn} ${idle}`} title="Export JSON"><Download size={14} /></button>
            <button onClick={importJSON} className={`${btn} ${idle}`} title="Import JSON"><Upload size={14} /></button>
            <button onClick={exportPDF} className={`${btn} ${idle}`} title="Export PDF documentation"><FileText size={14} /></button>
            <button onClick={centerView} className={`${btn} ${idle}`} title="Center view on schematic"><Crosshair size={14} /></button>
            <span className="font-mono text-[11px] opacity-50">{Math.round(camera.zoom * 100)}%</span>
            <div className="flex-1" />
            <button onClick={() => setDark((d) => !d)} className={`${btn} ${idle}`}>
              {dark ? <Sun size={14} /> : <Moon size={14} />}
            </button>
            <button onClick={clearAll} className={`${btn} text-red-500`} title="Clear all"><Trash2 size={14} /></button>
          </>
        )}
      </header>

      <main className="relative min-h-0 flex-1">
        <canvas ref={canvasRef} tabIndex={0} className="h-full w-full touch-none select-none outline-none"
          style={{ cursor: 'default' }}
          onPointerDown={onPointerDown} onPointerMove={onPointerMove}
          onPointerUp={onPointerUp} onPointerCancel={onPointerUp}
          onDoubleClick={onDoubleClick} onContextMenu={onContextMenu}
        />
      </main>

      <footer className={`z-20 flex shrink-0 items-stretch gap-4 overflow-x-auto border-t px-3 py-2 ${dark ? 'border-slate-700 bg-slate-800' : 'border-slate-200 bg-white'}`}>
        <section className="flex flex-col">
          <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">I/O</h3>
          <div className="flex items-center gap-1.5">
            {IO_BLOCKS.map((k) => (
              <button key={k} onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
                onContextMenu={(e) => { e.preventDefault(); setPaletteCtxMenu({ x: e.clientX, y: e.clientY, placement: { type: 'PRIMITIVE', kind: k } }) }}
                className={`${btn} ${isPrim(k) ? active : idle}`}>
                <span className={`grid h-7 w-7 place-items-center rounded text-xs font-bold ring-1 ${dark ? 'bg-slate-700 ring-slate-600' : 'bg-slate-100 ring-slate-200'}`}
                  style={{ color: GATE_EDGE[k] }}>
                  {k === 'INPUT' ? 'I'
                    : k === 'OUTPUT' ? <Lightbulb size={14} strokeWidth={2.25} />
                      : k === 'CLOCK' ? <Timer size={14} strokeWidth={2.25} />
                        : <Circle size={12} strokeWidth={2.5} />}
                </span>
                {k === 'INPUT' ? 'Toggle' : k === 'OUTPUT' ? 'Out' : k === 'CLOCK' ? 'Clock' : 'Button'}
              </button>
            ))}
          </div>
        </section>
        <div className={`my-1 w-px ${dark ? 'bg-slate-600' : 'bg-slate-200'}`} />
        <section className="flex flex-col">
          <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Gates</h3>
          <div className="flex items-center gap-1.5">
            {STANDARD_GATES.map((k) => (
              <button key={k} onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
                onContextMenu={(e) => { e.preventDefault(); setPaletteCtxMenu({ x: e.clientX, y: e.clientY, placement: { type: 'PRIMITIVE', kind: k } }) }}
                className={`${btn} ${isPrim(k) ? active : idle}`}>
                <span className={`grid h-7 w-7 place-items-center rounded text-sm font-bold ring-1 ${dark ? 'bg-slate-700 ring-slate-600' : 'bg-slate-100 ring-slate-200'}`}
                  style={{ color: GATE_EDGE[k] }}>
                  {GATE_GLYPH[k]}
                </span>
                {k}
              </button>
            ))}
          </div>
        </section>
        <div className={`my-1 w-px ${dark ? 'bg-slate-600' : 'bg-slate-200'}`} />
        <section className="flex flex-col">
          <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Flip-Flops</h3>
          <div className="flex items-center gap-1.5">
            {builtinChips.map((c) => (
              <button key={c.id} onClick={() => setPlacement({ type: 'CHIP', chipId: c.id })}
                onContextMenu={(e) => { e.preventDefault(); setPaletteCtxMenu({ x: e.clientX, y: e.clientY, placement: { type: 'CHIP', chipId: c.id } }) }}
                className={`${btn} ${isChip(c.id) ? active : idle}`}>
                <span className={`grid h-7 min-w-7 place-items-center rounded px-1 text-xs font-bold ring-1 ${dark ? 'bg-slate-700' : 'bg-slate-100'}`}
                  style={{ color: c.color, borderColor: c.color + '66' }}>
                  {c.name.slice(0, 2).toUpperCase()}
                </span>
                <span className="max-w-20 truncate">{c.name}</span>
              </button>
            ))}
          </div>
        </section>
        {customChips.length > 0 && (
          <>
            <div className={`my-1 w-px ${dark ? 'bg-slate-600' : 'bg-slate-200'}`} />
            <section className="flex min-w-0 flex-1 flex-col">
              <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Custom</h3>
              <div className="flex items-center gap-2.5 overflow-x-auto overflow-y-visible py-1">
                {customChips.map((c) => (
                  <div key={c.id} className="relative flex shrink-0 items-center">
                    <span
                      role="button"
                      tabIndex={0}
                      onClick={(e) => { e.stopPropagation(); enterEditChip(c.id) }}
                      onKeyDown={(e) => { if (e.key === 'Enter' || e.key === ' ') { e.stopPropagation(); enterEditChip(c.id) } }}
                      className={`absolute right-0.5 top-0.5 z-10 grid h-4 w-4 place-items-center rounded-full shadow ring-1 ${dark ? 'bg-slate-800 text-slate-200 ring-slate-600 hover:bg-slate-700' : 'bg-white text-slate-600 ring-slate-300 hover:bg-slate-50'}`}
                      title="Edit"
                    >
                      <Pencil size={10} />
                    </span>
                    <button
                      type="button"
                      onClick={() => setPlacement({ type: 'CHIP', chipId: c.id })}
                      onContextMenu={(e) => { e.preventDefault(); setPaletteCtxMenu({ x: e.clientX, y: e.clientY, placement: { type: 'CHIP', chipId: c.id } }) }}
                      className={`${btn} ${isChip(c.id) ? active : idle}`}
                    >
                      <span className={`grid h-7 min-w-7 place-items-center rounded px-1 text-xs font-bold ring-1 ${dark ? 'bg-slate-700' : 'bg-slate-100'}`}
                        style={{ color: c.color, borderColor: c.color + '66' }}>
                        {c.name.slice(0, 2).toUpperCase()}
                      </span>
                      <span className="max-w-20 truncate">{c.name}</span>
                    </button>
                  </div>
                ))}
              </div>
            </section>
          </>
        )}
      </footer>

      {paletteCtxMenu && (
        <div
          className={`fixed z-50 overflow-hidden rounded-lg border py-1 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}
          style={clampMenuPos(paletteCtxMenu.x, paletteCtxMenu.y, 160, 130)}
          onMouseLeave={() => setPaletteCtxMenu(null)}
        >
          <div className="px-3 py-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Quick Create</div>
          {[2, 4, 8].map((n) => (
            <button key={n} className={menuItemCls} onClick={() => batchCreate(paletteCtxMenu.placement, n)}>
              <Layers size={14} /> Create ×{n}
            </button>
          ))}
        </div>
      )}

      {ctxMenu && (
        <div
          className={`fixed z-50 overflow-hidden rounded-lg border py-1 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}
          style={clampMenuPos(ctxMenu.x, ctxMenu.y, 240, 360)}
          onMouseLeave={() => setCtxMenu(null)}
        >
          {ctxMenu.target === 'wire' ? (
            <>
              <button className="flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm text-red-500 hover:bg-red-50"
                onClick={() => ctxAction('delete')}>
                <Trash2 size={14} /> Delete wire
              </button>
            </>
          ) : (
            <>
              {[
                { a: 'cut', icon: <Scissors size={14} />, label: 'Cut', k: 'Ctrl+X' },
                { a: 'copy', icon: <Copy size={14} />, label: 'Copy', k: 'Ctrl+C' },
                { a: 'paste', icon: <ClipboardPaste size={14} />, label: 'Paste', k: 'Ctrl+V' },
              ].map((item) => (
                <button key={item.a} className={menuItemCls} onClick={() => ctxAction(item.a)}>
                  {item.icon} {item.label}
                  <span className="ml-auto text-[10px] opacity-50">{item.k}</span>
                </button>
              ))}
              <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
              <button className="flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm text-red-500 hover:bg-red-50"
                onClick={() => ctxAction('delete')}>
                <Trash2 size={14} /> Delete
              </button>

              {(ctxMenu.target === 'node' || ctxMenu.target === 'chip' || ctxMenu.target === 'unfoldedChip') && ctxMenu.nodeId && (
                <>
                  <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                  <button className={menuItemCls} onClick={() => ctxAction('changeBlock')}>
                    <Layers size={14} /> Change Block…
                  </button>
                </>
              )}

              {ctxMenu.target === 'node' && ctxMenu.nodeId && (() => {
                const n = nodes.find((x) => x.id === ctxMenu.nodeId)
                return n && (n.kind === 'INPUT' || n.kind === 'OUTPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK')
              })() && (
                  <>
                    <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                    <button className={menuItemCls} onClick={() => ctxAction('rename')}><Type size={14} /> Rename</button>
                  </>
                )}

              {ctxMenu.target === 'node' && ctxMenu.nodeId && (() => {
                const n = nodes.find((x) => x.id === ctxMenu.nodeId)
                return n && n.kind === 'CLOCK'
              })() && (() => {
                const n = nodes.find((x) => x.id === ctxMenu.nodeId)!
                const on = n.enabled !== false
                return (
                  <>
                    <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                    <button className={menuItemCls} onClick={() => ctxAction('toggleClock')}>
                      <Power size={14} /> {on ? 'Disable clock' : 'Enable clock'}
                    </button>
                    <button className={menuItemCls} onClick={() => ctxAction('clockSettings')}>
                      <Timer size={14} /> Clock settings…
                    </button>
                  </>
                )
              })()}

              {ctxMenu.target === 'node' && ctxMenu.nodeId && (
                <>
                  <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                  <div className="px-3 py-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Rotate</div>
                  <button className={menuItemCls} onClick={() => ctxAction('rotate90')}>
                    <RotateCw size={14} /> Rotate 90°
                  </button>
                  <button className={menuItemCls} onClick={() => ctxAction('rotate180')}>
                    <RotateCw size={14} /> Rotate 180°
                  </button>
                  <button className={menuItemCls} onClick={() => ctxAction('rotate270')}>
                    <RotateCw size={14} /> Rotate 270°
                  </button>
                </>
              )}

              {ctxMenu.target === 'chip' && (
                <>
                  <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                  <button className={menuItemCls} onClick={() => ctxAction('edit')}><Pencil size={14} /> Edit inner circuit</button>
                  <button className={menuItemCls} onClick={() => ctxAction('unfold')}>
                    <Maximize2 size={14} /> Unfold (inline)
                  </button>
                  <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                  <div className="px-3 py-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Rotate</div>
                  <button className={menuItemCls} onClick={() => ctxAction('rotate90')}>
                    <RotateCw size={14} /> Rotate 90°
                  </button>
                  <button className={menuItemCls} onClick={() => ctxAction('rotate180')}>
                    <RotateCw size={14} /> Rotate 180°
                  </button>
                  <button className={menuItemCls} onClick={() => ctxAction('rotate270')}>
                    <RotateCw size={14} /> Rotate 270°
                  </button>
                </>
              )}

              {ctxMenu.target === 'unfoldedChip' && (
                <>
                  <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                  <button className={menuItemCls} onClick={() => ctxAction('fold')}>
                    <Minimize2 size={14} /> Collapse / Fold Back
                  </button>
                  <button className={menuItemCls} onClick={() => ctxAction('edit')}>
                    <Pencil size={14} /> Edit inner circuit
                  </button>
                </>
              )}
            </>
          )}
        </div>
      )}

      {createModal && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/40">
          <div className={`w-80 rounded-xl border p-5 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}>
            <h2 className="mb-3 text-sm font-semibold">Create Custom Chip</h2>
            <label className="mb-1 block text-[11px] opacity-60">Name</label>
            <input autoFocus value={chipName} onChange={(e) => setChipName(e.target.value)}
              onKeyDown={(e) => { if (e.key === 'Enter') confirmCreateChip(); if (e.key === 'Escape') setCreateModal(false) }}
              className={`mb-4 w-full rounded-md border px-2.5 py-1.5 text-sm outline-none ${dark ? 'border-slate-600 bg-slate-900' : 'border-slate-200 bg-slate-50'}`}
            />
            <label className="mb-1.5 block text-[11px] opacity-60">Color</label>
            <div className="mb-2 flex flex-wrap gap-2">
              {CHIP_COLORS.map((c) => (
                <button key={c} onClick={() => { setChipColor(c); setCustomHex(c) }}
                  className={`h-7 w-7 rounded-full ring-2 ${chipColor === c ? 'ring-slate-800 ring-offset-1' : 'ring-transparent'}`}
                  style={{ background: c }} />
              ))}
            </div>
            <div className="mb-5 flex items-center gap-2">
              <input type="color" value={customHex} onChange={(e) => { setCustomHex(e.target.value); setChipColor(e.target.value) }}
                className="h-8 w-10 cursor-pointer rounded border-0" />
              <span className="text-[11px] opacity-60">Custom color</span>
            </div>
            <div className="flex justify-end gap-2">
              <button onClick={() => setCreateModal(false)} className={`${btn} ${idle}`}>Cancel</button>
              <button onClick={confirmCreateChip} className={`${btn} bg-blue-50 text-blue-700`}>Create</button>
            </div>
          </div>
        </div>
      )}

      {clockModal && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/40">
          <div className={`w-72 rounded-xl border p-5 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}>
            <h2 className="mb-3 text-sm font-semibold">Clock Frequency</h2>
            <label className="mb-1 block text-[11px] opacity-60">
              Period (ticks @ 60 TPS) → {(60 / Math.max(2, clockModal.period)).toFixed(2)} Hz
            </label>
            <input type="range" min={4} max={240} value={clockModal.period}
              onChange={(e) => setClockModal({ ...clockModal, period: Number(e.target.value) })}
              className="mb-2 w-full" />
            <input type="number" min={2} max={600} value={clockModal.period}
              onChange={(e) => setClockModal({ ...clockModal, period: Math.max(2, Number(e.target.value) || 30) })}
              className={`mb-4 w-full rounded-md border px-2.5 py-1.5 text-sm outline-none ${dark ? 'border-slate-600 bg-slate-900' : 'border-slate-200 bg-slate-50'}`}
            />
            <div className="flex justify-end gap-2">
              <button onClick={() => setClockModal(null)} className={`${btn} ${idle}`}>Cancel</button>
              <button onClick={() => {
                setNodes((ns) => ns.map((n) => n.id === clockModal.id ? { ...n, period: clockModal.period } : n))
                setClockModal(null)
              }} className={`${btn} bg-blue-50 text-blue-700`}>Apply</button>
            </div>
          </div>
        </div>
      )}

      {renamePinModal && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/40">
          <div className={`w-72 rounded-xl border p-5 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}>
            <h2 className="mb-3 text-sm font-semibold">Rename Pin</h2>
            <input autoFocus value={renamePinModal.name}
              onChange={(e) => setRenamePinModal({ ...renamePinModal, name: e.target.value })}
              onKeyDown={(e) => { if (e.key === 'Enter') applyPinRename(); if (e.key === 'Escape') setRenamePinModal(null) }}
              className={`mb-4 w-full rounded-md border px-2.5 py-1.5 text-sm outline-none ${dark ? 'border-slate-600 bg-slate-900' : 'border-slate-200 bg-slate-50'}`}
            />
            <div className="flex justify-end gap-2">
              <button onClick={() => setRenamePinModal(null)} className={`${btn} ${idle}`}>Cancel</button>
              <button onClick={applyPinRename} className={`${btn} bg-blue-50 text-blue-700`}>Rename</button>
            </div>
          </div>
        </div>
      )}

      {changeBlockModal && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/40">
          <div className={`w-80 rounded-xl border p-4 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}>
            <h2 className="mb-1 text-sm font-semibold">Change Component</h2>
            <p className="mb-3 text-[11px] opacity-60">Wires are re-mapped by pin index. Label resets to the new default.</p>

            <div className="max-h-[280px] overflow-y-auto pr-1">
              <div className="mb-1 px-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">I/O</div>
              <div className="mb-3 flex flex-col gap-0.5">
                {IO_BLOCKS.map((k) => (
                  <button key={k} className={menuItemCls}
                    onClick={() => applyNodeReplacement(changeBlockModal.nodeId, { type: 'PRIMITIVE', kind: k })}>
                    <span className="inline-block h-2.5 w-2.5 rounded-sm" style={{ background: GATE_EDGE[k] }} />
                    {k === 'INPUT' ? 'Toggle' : k === 'OUTPUT' ? 'Out' : k === 'CLOCK' ? 'Clock' : 'Button'}
                  </button>
                ))}
              </div>

              <div className="mb-1 px-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Standard Gates</div>
              <div className="mb-3 flex flex-col gap-0.5">
                {STANDARD_GATES.map((k) => (
                  <button key={k} className={menuItemCls}
                    onClick={() => applyNodeReplacement(changeBlockModal.nodeId, { type: 'PRIMITIVE', kind: k })}>
                    <span className="inline-block h-2.5 w-2.5 rounded-sm" style={{ background: GATE_EDGE[k] }} />
                    {k}
                  </button>
                ))}
                {builtinChips.map((c) => (
                  <button key={c.id} className={menuItemCls}
                    onClick={() => applyNodeReplacement(changeBlockModal.nodeId, { type: 'CHIP', chipId: c.id })}>
                    <span className="inline-block h-2.5 w-2.5 rounded-full" style={{ background: c.color }} />
                    {c.name}
                  </button>
                ))}
              </div>

              {customChips.length > 0 && (
                <>
                  <div className="mb-1 px-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Custom Chips</div>
                  <div className="flex flex-col gap-0.5">
                    {customChips.map((c) => (
                      <button key={c.id} className={menuItemCls}
                        onClick={() => applyNodeReplacement(changeBlockModal.nodeId, { type: 'CHIP', chipId: c.id })}>
                        <span className="inline-block h-2.5 w-2.5 rounded-full" style={{ background: c.color }} />
                        {c.name}
                      </button>
                    ))}
                  </div>
                </>
              )}
            </div>

            <div className="mt-3 flex justify-end">
              <button onClick={() => setChangeBlockModal(null)} className={`${btn} ${idle}`}>Cancel</button>
            </div>
          </div>
        </div>
      )}
    </div>
  )
}