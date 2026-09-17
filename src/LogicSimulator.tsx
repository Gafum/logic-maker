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
 *  LogicMaker — refactored (orthogonal wires, inline unfold, English UI)
 * ===================================================================== */

type PinSide = 'in' | 'out'
interface Vec2 { x: number; y: number }
interface PinRef { nodeId: string; pinId: string; side: PinSide }
type PrimitiveType =
  | 'AND' | 'OR' | 'NOT'
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
  /** CLOCK: period in sim ticks (60 TPS) */
  period?: number
  /** CLOCK / BUTTON: enabled state */
  enabled?: boolean
  /** Rotation in degrees: 0 | 90 | 180 | 270 */
  rotation?: 0 | 90 | 180 | 270
  /** Inline unfold state for CHIP nodes */
  unfolded?: boolean
  unfoldedSize?: { w: number; h: number }
}
interface Wire {
  id: string
  from: PinRef
  to: PinRef
  /** optional routing control points the path must pass through */
  mids?: Vec2[]
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
  snapSelected: Set<string>
  snapCamera: Camera
}
interface HistoryEntry { nodes: CircuitNode[]; wires: Wire[] }
interface ContextMenuState {
  x: number
  y: number
  world: Vec2
  target: 'canvas' | 'node' | 'wire' | 'chip' | 'waypoint' | 'unfoldedChip'
  nodeId?: string
  wireId?: string
  waypointIndex?: number
}

const pinKey = (n: string, p: string) => `${n}:${p}`
const isPinRefEqual = (a: PinRef, b: PinRef) =>
  a.nodeId === b.nodeId && a.pinId === b.pinId && a.side === b.side

/* Geometry */
const GRID = 24
/** Pins live on the half-grid so H/V alignments produce perfectly straight wires. */
const HALF_GRID = GRID / 2
const NODE_W_MIN = 80
const NODE_PAD = 12
const PIN_SPACING = 24 // multiple of HALF_GRID → pins stay on sub-grid
const PIN_R = 5.5
const MIN_ZOOM = 0.05
const MAX_ZOOM = 4
/** Padding kept between a routed wire and any node body it must bypass. */
const ROUTE_PAD = 18

let idCounter = 0
const uid = (prefix = 'n') =>
  `${prefix}_${(idCounter++).toString(36)}_${Math.random().toString(36).slice(2, 6)}`
const clamp = (v: number, lo: number, hi: number) => Math.min(hi, Math.max(lo, v))
const snap = (v: number) => Math.round(v / GRID) * GRID
const snapHalf = (v: number) => Math.round(v / HALF_GRID) * HALF_GRID

function approxLabelWidth(label: string): number {
  return Math.ceil(label.length * 5) + 40
}

const nodeRows = (n: CircuitNode) => Math.max(n.inputs.length, n.outputs.length, 1)
const nodeHeight = (n: CircuitNode) => {
  if (n.kind === 'CHIP' && n.unfolded && n.unfoldedSize) return n.unfoldedSize.h
  return NODE_PAD * 2 + PIN_SPACING * Math.max(nodeRows(n) - 1, 0) + PIN_SPACING
}
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
    n.kind === 'INPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK' ? 60 : 0
  const outReserve = n.kind === 'OUTPUT' ? 28 : 0
  return Math.max(NODE_W_MIN, fromLabel + btnReserve + outReserve + pinExtra)
}
const nodeBox = (n: CircuitNode) => ({
  x: n.position.x, y: n.position.y, w: nodeWidth(n), h: nodeHeight(n),
})

/**
 * Pin position on a node's edge, aware of rotation.
 * Rotation only changes WHICH edge a logical side (in/out) is drawn on —
 * the node body itself stays axis-aligned.
 */
function pinPos(n: CircuitNode, side: PinSide, index: number, count: number): Vec2 {
  const b = nodeBox(n)
  const rot = n.rotation || 0
  let edge: 'left' | 'right' | 'top' | 'bottom'
  if (rot === 90) edge = side === 'in' ? 'top' : 'bottom'
  else if (rot === 180) edge = side === 'in' ? 'right' : 'left'
  else if (rot === 270) edge = side === 'in' ? 'bottom' : 'top'
  else edge = side === 'in' ? 'left' : 'right'

  if (edge === 'left' || edge === 'right') {
    const x = edge === 'left' ? b.x : b.x + b.w
    const y = count <= 1
      ? snapHalf(b.y + b.h / 2)
      : snapHalf(b.y + NODE_PAD + PIN_SPACING / 2 + ((b.h - NODE_PAD * 2 - PIN_SPACING) * index) / (count - 1))
    return { x, y }
  }
  const y = edge === 'top' ? b.y : b.y + b.h
  const x = count <= 1
    ? snapHalf(b.x + b.w / 2)
    : snapHalf(b.x + NODE_PAD + PIN_SPACING / 2 + ((b.w - NODE_PAD * 2 - PIN_SPACING) * index) / (count - 1))
  return { x, y }
}
const leftPinPos = (n: CircuitNode, i: number): Vec2 => pinPos(n, 'in', i, n.inputs.length)
const rightPinPos = (n: CircuitNode, i: number): Vec2 => pinPos(n, 'out', i, n.outputs.length)

interface EnumeratedPin {
  nodeId: string; pinId: string; side: PinSide; index: number; pos: Vec2; node: CircuitNode
}
const enumeratePins = (n: CircuitNode): EnumeratedPin[] => {
  const list: EnumeratedPin[] = []
  n.inputs.forEach((p, i) =>
    list.push({ nodeId: n.id, pinId: p.id, side: 'in', index: i, pos: leftPinPos(n, i), node: n }),
  )
  n.outputs.forEach((p, i) =>
    list.push({ nodeId: n.id, pinId: p.id, side: 'out', index: i, pos: rightPinPos(n, i), node: n }),
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
  INPUT: { label: 'IN', inputs: [], outputs: ['OUT'] },
  OUTPUT: { label: 'OUT', inputs: ['IN'], outputs: [] },
  CLOCK: { label: 'CLK', inputs: [], outputs: ['OUT'] },
  BUTTON: { label: 'BTN', inputs: [], outputs: ['OUT'] },
}

const GATE_EDGE: Record<string, string> = {
  AND: '#059669',
  OR: '#2563eb',
  NOT: '#dc2626',
  INPUT: '#64748b',
  OUTPUT: '#64748b',
  CLOCK: '#7c3aed',
  BUTTON: '#d97706',
}

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

const createWire = (from: PinRef, to: PinRef, mids?: Vec2[]): Wire =>
  ({ id: uid('w'), from, to, ...(mids?.length ? { mids } : {}) })

/* Built-ins */
const outRef = (id: string, pin: string): PinRef => ({ nodeId: id, pinId: pin, side: 'out' })
const inRef = (id: string, pin: string): PinRef => ({ nodeId: id, pinId: pin, side: 'in' })
const U = (col: number, row: number): Vec2 => ({ x: col * 150, y: row * 110 })

function buildRsLatch(): ChipDefinition {
  const R = createPrimitiveNode('INPUT', U(0, 0), 'R')
  const S = createPrimitiveNode('INPUT', U(0, 2), 'S')
  const orQ = createPrimitiveNode('OR', U(2, 0), 'NOR')
  const orQb = createPrimitiveNode('OR', U(2, 2), 'NOR')
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

/* Compiler */
interface CompiledGate {
  key: string
  type: 'AND' | 'OR' | 'NOT'
  inputs: (string | null)[]
  out: string
}
interface CompiledCircuit {
  gates: CompiledGate[]
  inputNets: Record<string, string>
  pinNets: Record<string, string | null>
}

const MAX_DEPTH = 24

function compileCircuit(
  circuit: { nodes: CircuitNode[]; wires: Wire[] },
  chips: Record<string, ChipDefinition>,
): CompiledCircuit {
  const gates: CompiledGate[] = []
  const drivers = new Map<string, string>()
  const aliases = new Map<string, string>()
  const inputNets: Record<string, string> = {}
  const gateInputKeys = new Map<string, string[]>()

  const walk = (c: { nodes: CircuitNode[]; wires: Wire[] }, prefix: string, depth: number) => {
    for (const w of c.wires) {
      drivers.set(
        pinKey(prefix + w.to.nodeId, w.to.pinId),
        pinKey(prefix + w.from.nodeId, w.from.pinId),
      )
    }
    for (const node of c.nodes) {
      const id = prefix + node.id
      switch (node.kind) {
        case 'AND': case 'OR': case 'NOT': {
          gates.push({ key: id, type: node.kind, inputs: [], out: pinKey(id, node.outputs[0].id) })
          gateInputKeys.set(id, node.inputs.map((p) => pinKey(id, p.id)))
          break
        }
        case 'INPUT': case 'CLOCK': case 'BUTTON':
          if (prefix === '') inputNets[node.id] = pinKey(id, 'out')
          break
        case 'OUTPUT': break
        case 'CHIP': {
          const chip = node.chipId ? chips[node.chipId] : undefined
          if (!chip || depth >= MAX_DEPTH) break
          const inner = `${id}/`
          chip.inputNodeIds.forEach((innerId, i) => {
            aliases.set(pinKey(inner + innerId, 'out'), pinKey(id, `i${i}`))
          })
          chip.outputNodeIds.forEach((innerId, i) => {
            aliases.set(pinKey(id, `o${i}`), pinKey(inner + innerId, 'in'))
          })
          walk({ nodes: chip.nodes, wires: chip.wires }, inner, depth + 1)
          break
        }
      }
    }
  }
  walk(circuit, '', 0)

  const memo = new Map<string, string | null>()
  const resolveOut = (outKey: string, seen: Set<string>): string | null => {
    if (memo.has(outKey)) return memo.get(outKey)!
    const alias = aliases.get(outKey)
    if (alias) {
      const v = netOfInput(alias, seen)
      memo.set(outKey, v)
      return v
    }
    memo.set(outKey, outKey)
    return outKey
  }
  const netOfInput = (inKey: string, seen: Set<string>): string | null => {
    if (seen.has(inKey)) return null
    seen.add(inKey)
    const drive = drivers.get(inKey)
    if (drive === undefined) {
      const alias = aliases.get(inKey)
      if (alias) {
        const v = netOfInput(alias, seen)
        seen.delete(inKey)
        return v
      }
      seen.delete(inKey)
      return null
    }
    const result = resolveOut(drive, seen)
    seen.delete(inKey)
    return result
  }
  const resolveIn = (inKey: string): string | null => {
    if (memo.has(inKey)) return memo.get(inKey)!
    const v = netOfInput(inKey, new Set())
    memo.set(inKey, v)
    return v
  }

  for (const g of gates) {
    const keys = gateInputKeys.get(g.key) ?? []
    g.inputs = keys.map((k) => resolveIn(k))
  }

  const pinNets: Record<string, string | null> = {}
  for (const node of circuit.nodes) {
    for (const p of node.inputs) pinNets[pinKey(node.id, p.id)] = resolveIn(pinKey(node.id, p.id))
    for (const p of node.outputs) pinNets[pinKey(node.id, p.id)] = resolveOut(pinKey(node.id, p.id), new Set())
  }
  return { gates, inputNets, pinNets }
}

/* Simulator */
const SETTLE_PASSES = 80
const SIM_TPS = 60

class Simulator {
  private state = new Map<string, boolean>()
  private compiled: CompiledCircuit = { gates: [], inputNets: {}, pinNets: {} }
  private tickCount = 0

  load(c: CompiledCircuit) {
    const next = new Map<string, boolean>()
    for (const g of c.gates) next.set(g.out, this.state.get(g.out) ?? false)
    for (const net of Object.values(c.inputNets)) next.set(net, this.state.get(net) ?? false)
    this.state = next
    this.compiled = c
  }
  reset() { for (const k of this.state.keys()) this.state.set(k, false); this.tickCount = 0 }

  private applyInputs(nodes: CircuitNode[]) {
    for (const n of nodes) {
      if (n.kind === 'INPUT' || n.kind === 'BUTTON') {
        const net = this.compiled.inputNets[n.id]
        if (net) this.state.set(net, !!n.value)
      } else if (n.kind === 'CLOCK') {
        const net = this.compiled.inputNets[n.id]
        if (net) {
          if (n.enabled === false) {
            this.state.set(net, false)
          } else {
            const period = Math.max(2, n.period ?? 30)
            const half = Math.floor(period / 2)
            this.state.set(net, (this.tickCount % period) < half)
          }
        }
      }
    }
  }
  private read(net: string | null) { return net === null ? false : (this.state.get(net) ?? false) }

  tick(nodes: CircuitNode[]) {
    this.tickCount++
    this.applyInputs(nodes)
    const { gates } = this.compiled
    for (let pass = 0; pass < SETTLE_PASSES; pass++) {
      let changed = false
      const results = new Array<boolean>(gates.length)
      for (let i = 0; i < gates.length; i++) {
        const g = gates[i]
        switch (g.type) {
          case 'AND': results[i] = this.read(g.inputs[0]) && this.read(g.inputs[1]); break
          case 'OR': results[i] = this.read(g.inputs[0]) || this.read(g.inputs[1]); break
          case 'NOT': results[i] = !this.read(g.inputs[0]); break
        }
      }
      for (let i = 0; i < gates.length; i++) {
        if (this.state.get(gates[i].out) !== results[i]) {
          this.state.set(gates[i].out, results[i]); changed = true
        }
      }
      if (!changed) break
    }
  }
  snapshot(): SignalMap {
    const out: SignalMap = {}
    for (const [k, net] of Object.entries(this.compiled.pinNets)) out[k] = this.read(net)
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

/* =========================================================
 *  Orthogonal / Manhattan wire routing
 * ========================================================= */

/** Axis-aligned rect inflated by ROUTE_PAD (used for obstacle tests). */
function inflatedBox(n: CircuitNode): { x: number; y: number; w: number; h: number } {
  const b = nodeBox(n)
  return { x: b.x - ROUTE_PAD, y: b.y - ROUTE_PAD, w: b.w + ROUTE_PAD * 2, h: b.h + ROUTE_PAD * 2 }
}

/** Does the open segment (p0→p1) intersect the interior of box? */
function segmentHitsBox(p0: Vec2, p1: Vec2, box: { x: number; y: number; w: number; h: number }): boolean {
  // Quick reject: both ends outside same side
  const minX = Math.min(p0.x, p1.x), maxX = Math.max(p0.x, p1.x)
  const minY = Math.min(p0.y, p1.y), maxY = Math.max(p0.y, p1.y)
  if (maxX < box.x || minX > box.x + box.w || maxY < box.y || minY > box.y + box.h) return false
  // Horizontal or vertical segment – clamp and test
  if (Math.abs(p0.y - p1.y) < 0.5) {
    // horizontal
    const y = p0.y
    return y > box.y && y < box.y + box.h && maxX > box.x && minX < box.x + box.w
  }
  if (Math.abs(p0.x - p1.x) < 0.5) {
    const x = p0.x
    return x > box.x && x < box.x + box.w && maxY > box.y && minY < box.y + box.h
  }
  return true // diagonal shouldn't happen
}

function pathHitsAny(pts: Vec2[], obstacles: { x: number; y: number; w: number; h: number }[]): boolean {
  for (let i = 0; i < pts.length - 1; i++) {
    for (const box of obstacles) {
      if (segmentHitsBox(pts[i], pts[i + 1], box)) return true
    }
  }
  return false
}

/**
 * Build a strictly orthogonal (H/V) polyline from `a` to `b`.
 * - With user waypoints: routes leg-by-leg.
 * - Without waypoints: tries several Manhattan candidates and picks the first
 *   that does not cross any obstacle box (node body + ROUTE_PAD).
 * - When start/end share an axis, returns a single straight segment (no stairs).
 * Collinear points are collapsed automatically.
 */
function orthogonalPath(
  a: Vec2,
  b: Vec2,
  mids?: Vec2[],
  obstacles?: { x: number; y: number; w: number; h: number }[],
): Vec2[] {
  const collapse = (pts: Vec2[]): Vec2[] => {
    const out: Vec2[] = []
    for (const p of pts) {
      if (out.length >= 2) {
        const a0 = out[out.length - 2]
        const a1 = out[out.length - 1]
        if (Math.hypot(p.x - a1.x, p.y - a1.y) <= 0.5) continue
        const horiz = Math.abs(a0.y - a1.y) <= 0.5 && Math.abs(a1.y - p.y) <= 0.5
        const vert = Math.abs(a0.x - a1.x) <= 0.5 && Math.abs(a1.x - p.x) <= 0.5
        if (horiz || vert) { out[out.length - 1] = p; continue }
      } else if (out.length === 1) {
        if (Math.hypot(p.x - out[0].x, p.y - out[0].y) <= 0.5) continue
      }
      out.push(p)
    }
    return out
  }

  // Straight when already axis-aligned
  if (!mids?.length && (Math.abs(a.x - b.x) < 0.5 || Math.abs(a.y - b.y) < 0.5)) {
    return collapse([a, b])
  }

  // With explicit waypoints – simple L-bends between anchors
  if (mids?.length) {
    const result: Vec2[] = [a]
    let cur = a
    for (const t of [...mids, b]) {
      const dx = t.x - cur.x, dy = t.y - cur.y
      if (Math.abs(dx) > 0.5 && Math.abs(dy) > 0.5) {
        if (Math.abs(dx) >= Math.abs(dy)) result.push({ x: t.x, y: cur.y })
        else result.push({ x: cur.x, y: t.y })
      }
      result.push(t)
      cur = t
    }
    return collapse(result)
  }

  // Automatic obstacle-aware Manhattan candidates
  const candidates: Vec2[][] = []
  // Classic mid-split H-V-H
  {
    const mx = snapHalf((a.x + b.x) / 2)
    candidates.push([a, { x: mx, y: a.y }, { x: mx, y: b.y }, b])
  }
  // Classic mid-split V-H-V
  {
    const my = snapHalf((a.y + b.y) / 2)
    candidates.push([a, { x: a.x, y: my }, { x: b.x, y: my }, b])
  }
  // Go via left/right/top/bottom of each obstacle (simple bypass)
  if (obstacles?.length) {
    for (const box of obstacles) {
      const left = box.x
      const right = box.x + box.w
      const top = box.y
      const bot = box.y + box.h
      // route above
      candidates.push([a, { x: a.x, y: top }, { x: b.x, y: top }, b])
      // route below
      candidates.push([a, { x: a.x, y: bot }, { x: b.x, y: bot }, b])
      // route left
      candidates.push([a, { x: left, y: a.y }, { x: left, y: b.y }, b])
      // route right
      candidates.push([a, { x: right, y: a.y }, { x: right, y: b.y }, b])
    }
  }
  // Fallback simple L
  candidates.push([a, { x: b.x, y: a.y }, b])
  candidates.push([a, { x: a.x, y: b.y }, b])

  let best: Vec2[] | null = null
  let bestLen = Infinity
  for (const raw of candidates) {
    const pts = collapse(raw)
    if (obstacles?.length && pathHitsAny(pts, obstacles)) continue
    // length = sum of segment lengths
    let len = 0
    for (let i = 0; i < pts.length - 1; i++)
      len += Math.abs(pts[i + 1].x - pts[i].x) + Math.abs(pts[i + 1].y - pts[i].y)
    if (len < bestLen) { bestLen = len; best = pts }
  }
  return best ?? collapse([a, { x: b.x, y: a.y }, b])
}

/** Project point P onto segment AB. */
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

function insertMidAtClick(
  anchors: Vec2[],
  existingMids: Vec2[] | undefined,
  click: Vec2,
): Vec2[] {
  const mids = existingMids ? [...existingMids] : []
  if (anchors.length < 2) return [...mids, click]

  let bestSeg = 0
  let bestDist = Infinity
  let bestPoint = click
  for (let i = 0; i < anchors.length - 1; i++) {
    const proj = projectOnSegment(click, anchors[i], anchors[i + 1])
    if (proj.dist < bestDist) {
      bestDist = proj.dist
      bestSeg = i
      bestPoint = proj.point
    }
  }
  // Insert into mids array (segment i corresponds to mids index i)
  // segment count in the polyline is >= mids count; approximate by using bestSeg
  // clamped to mids array bounds.
  const insertIdx = Math.min(bestSeg, mids.length)
  mids.splice(insertIdx, 0, bestPoint)
  return mids
}

function drawBody(
  ctx: CanvasRenderingContext2D, n: CircuitNode,
  fill: string, edge: string | null,
  selected: boolean, zoom: number, theme: Theme,
) {
  const b = nodeBox(n)
  const r = 3 // crisp semi-sharp industrial corners
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
    const btnW = 44, btnH = 24
    const nw = nodeWidth(n)
    const bx = n.position.x + nw - btnW - 12
    const by = n.position.y + (b.h - btnH) / 2
    const disabled = n.kind === 'CLOCK' && n.enabled === false
    ctx.fillStyle = value ? theme.wireHigh : (dark ? '#3f3f46' : '#e2e8f0')
    roundRect(ctx, bx, by, btnW, btnH, 3); ctx.fill()
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
    ctx.rect(n.position.x + 8, n.position.y, bx - n.position.x - 10, b.h)
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
    const cy = n.position.y + b.h / 2, cx = n.position.x + nw - 28
    if (value) { ctx.save(); ctx.shadowColor = theme.wireHigh + '80'; ctx.shadowBlur = 14 }
    ctx.beginPath()
    ctx.arc(cx, cy - 2, 9, 0, Math.PI * 2)
    ctx.fillStyle = value ? theme.wireHigh : (dark ? '#334155' : '#cbd5e1'); ctx.fill()
    ctx.strokeStyle = value ? theme.wireHigh : theme.pinLow; ctx.lineWidth = 1.5; ctx.stroke()
    ctx.beginPath()
    ctx.moveTo(cx - 5, cy + 7); ctx.lineTo(cx + 5, cy + 7)
    ctx.lineTo(cx + 3.5, cy + 11); ctx.lineTo(cx - 3.5, cy + 11)
    ctx.closePath()
    ctx.fillStyle = value ? theme.wireHigh : (dark ? '#475569' : '#94a3b8')
    ctx.fill()
    if (value) ctx.restore()
    ctx.fillStyle = theme.label
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'left'; ctx.textBaseline = 'middle'
    ctx.save()
    ctx.beginPath()
    ctx.rect(n.position.x + 8, n.position.y, cx - n.position.x - 16, b.h)
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

  // gates
  drawBody(ctx, n, fill, edge, selected, zoom, theme)
  const cx = n.position.x + b.w / 2, cy = n.position.y + b.h / 2
  const glyph = n.kind === 'AND' ? '∧' : n.kind === 'OR' ? '∨' : '¬'
  ctx.fillStyle = edge ?? theme.edge
  ctx.font = '800 28px ui-sans-serif, system-ui, sans-serif'
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle'
  ctx.fillText(glyph, cx, cy + 1)
  ctx.fillStyle = theme.label
  ctx.font = '600 10px ui-sans-serif, system-ui, sans-serif'
  ctx.fillText(n.label, cx, n.position.y + 14)
  ctx.restore()
}

function drawPin(ctx: CanvasRenderingContext2D, x: number, y: number, high: boolean, zoom: number, theme: Theme) {
  ctx.beginPath(); ctx.arc(x, y, PIN_R, 0, Math.PI * 2)
  ctx.fillStyle = high ? theme.pinHigh : (theme.body === '#ffffff' ? '#e2e8f0' : '#52525b')
  ctx.fill()
  ctx.strokeStyle = high ? theme.pinHigh : theme.pinLow
  ctx.lineWidth = 1.3 / zoom; ctx.stroke()
}

function pinAnchor(n: CircuitNode, w: { side: PinSide; pinId: string }): Vec2 | null {
  if (w.side === 'out') {
    const i = n.outputs.findIndex((p) => p.id === w.pinId)
    return i >= 0 ? rightPinPos(n, i) : null
  }
  const i = n.inputs.findIndex((p) => p.id === w.pinId)
  return i >= 0 ? leftPinPos(n, i) : null
}

function wireView(
  from: CircuitNode,
  to: CircuitNode,
  w: Wire,
  allNodes?: CircuitNode[],
) {
  const a = pinAnchor(from, w.from)
  const b = pinAnchor(to, w.to)
  if (!a || !b) return null
  // Obstacles = every node except the two endpoints (so the wire can leave/enter pins)
  const obstacles = allNodes
    ?.filter((n) => n.id !== from.id && n.id !== to.id)
    .map(inflatedBox)
  const pts = orthogonalPath(a, b, w.mids, obstacles)
  return { pts }
}

function strokeWirePath(ctx: CanvasRenderingContext2D, pts: Vec2[]) {
  if (pts.length < 2) return
  ctx.beginPath()
  ctx.moveTo(pts[0].x, pts[0].y)
  for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y)
}

/** Draw the expanded inline view of a chip on the canvas. */
function drawUnfoldedChip(
  ctx: CanvasRenderingContext2D, n: CircuitNode, chip: ChipDefinition,
  selected: boolean, signal: SignalMap,
  chipMeta: Record<string, { color: string }>,
  zoom: number, theme: Theme, dark: boolean,
) {
  const b = nodeBox(n)
  const col = chip.color

  // Background card (fixed position – does not push neighbours)
  ctx.fillStyle = dark ? 'rgba(30,30,36,0.92)' : 'rgba(255,255,255,0.94)'
  roundRect(ctx, b.x, b.y, b.w, b.h, 4)
  ctx.fill()

  // Outer dashed boundary
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

  // Header background
  ctx.save()
  ctx.beginPath()
  roundRect(ctx, b.x, b.y, b.w, 26, 4)
  ctx.clip()
  ctx.fillStyle = dark ? shade(col, -0.55) : shade(col, 0.85)
  ctx.fillRect(b.x, b.y, b.w, 26)
  ctx.restore()

  // Header label
  ctx.fillStyle = theme.label
  ctx.font = '700 11px ui-sans-serif, system-ui, sans-serif'
  ctx.textAlign = 'left'
  ctx.textBaseline = 'middle'
  ctx.fillText(`${chip.name.toUpperCase()} — UNFOLDED`, b.x + 12, b.y + 13)

  // Collapse button (top-right)
  const btnW = 74, btnH = 18
  const bx = b.x + b.w - btnW - 8
  const by = b.y + 4
  ctx.fillStyle = dark ? '#334155' : '#ffffff'
  roundRect(ctx, bx, by, btnW, btnH, 3)
  ctx.fill()
  ctx.strokeStyle = col
  ctx.lineWidth = 1 / zoom
  ctx.stroke()
  ctx.fillStyle = theme.label
  ctx.font = '600 10px ui-sans-serif, system-ui, sans-serif'
  ctx.textAlign = 'center'
  ctx.fillText('Collapse', bx + btnW / 2, by + btnH / 2 + 0.5)

  // Inner content layout
  if (!chip.nodes.length) {
    ctx.fillStyle = theme.label
    ctx.font = '500 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'
    ctx.fillText('(empty)', b.x + b.w / 2, b.y + b.h / 2)
    return
  }
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
  const byId = new Map(translated.map((cn) => [cn.id, cn]))

  // Inner wires
  for (const w of chip.wires) {
    const from = byId.get(w.from.nodeId)
    const to = byId.get(w.to.nodeId)
    if (!from || !to) continue
    const vw = wireView(from, to, w, translated)
    if (!vw) continue
    ctx.strokeStyle = theme.wireLow
    ctx.lineWidth = clamp(1.8 / zoom, 1, 2.4)
    strokeWirePath(ctx, vw.pts)
    ctx.stroke()
  }

  // Inner nodes (ghosted)
  for (const cn of translated) {
    drawNode(ctx, cn, false, signal, chipMeta, zoom, theme, dark, 0.9)
    for (const pin of enumeratePins(cn)) {
      drawPin(ctx, pin.pos.x, pin.pos.y, false, zoom, theme)
    }
  }
}

function drawScene(
  ctx: CanvasRenderingContext2D, sw: number, sh: number, dpr: number,
  cam: Camera, nodes: CircuitNode[], wires: Wire[], signal: SignalMap,
  selected: Set<string>, selectedWireId: string | null, selectedWireIds: Set<string>, hoverWireId: string | null,
  selectedMids: Set<string>,
  chipMeta: Record<string, { color: string }>,
  chipById: Record<string, ChipDefinition>,
  pending: { start: PinRef; startPos: Vec2; end: Vec2 } | null,
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

  const byId = new Map(nodes.map((n) => [n.id, n]))
  const wireActive = (w: Wire) => !!signal[pinKey(w.from.nodeId, w.from.pinId)]

  // Pre-compute all polylines once (with obstacle avoidance)
  const wirePolys: { w: Wire; pts: Vec2[]; high: boolean; hover: boolean; isSel: boolean }[] = []
  for (const w of wires) {
    const from = byId.get(w.from.nodeId), to = byId.get(w.to.nodeId)
    if (!from || !to) continue
    const vw = wireView(from, to, w, nodes)
    if (!vw) continue
    wirePolys.push({
      w,
      pts: vw.pts,
      high: wireActive(w),
      hover: hoverWireId === w.id,
      isSel: selectedWireId === w.id || selectedWireIds.has(w.id),
    })
  }

  // Collect unique horizontal lanes: key = rounded Y, value = list of [xMin,xMax] intervals
  // Used both to avoid drawing duplicate overlapping horizontals and to place a single jumper per Y.
  type HSeg = { y: number; x0: number; x1: number; high: boolean; hover: boolean; isSel: boolean }
  const hSegs: HSeg[] = []
  for (const { pts, high, hover, isSel } of wirePolys) {
    for (let i = 0; i < pts.length - 1; i++) {
      const p0 = pts[i], p1 = pts[i + 1]
      if (Math.abs(p0.y - p1.y) > 0.5) continue
      hSegs.push({
        y: p0.y,
        x0: Math.min(p0.x, p1.x),
        x1: Math.max(p0.x, p1.x),
        high, hover, isSel,
      })
    }
  }

  // Pass 1 – horizontal segments (solid priority). Merge near-identical Y so parallel
  // overlapping runs don't stack into thick double strokes.
  const drawnH = new Set<string>()
  for (const seg of hSegs) {
    const yKey = Math.round(seg.y)
    const key = `${yKey}:${Math.round(seg.x0)}:${Math.round(seg.x1)}`
    if (drawnH.has(key)) continue
    drawnH.add(key)
    if (seg.high) {
      ctx.save(); ctx.strokeStyle = theme.wireHigh + '30'; ctx.lineWidth = 7 / zoom
      ctx.beginPath(); ctx.moveTo(seg.x0, seg.y); ctx.lineTo(seg.x1, seg.y); ctx.stroke(); ctx.restore()
    }
    ctx.strokeStyle = seg.isSel ? theme.sel : seg.hover ? theme.wireHover : seg.high ? theme.wireHigh : theme.wireLow
    ctx.lineWidth = seg.isSel ? clamp(3 / zoom, 1.6, 3.4) : clamp(2.1 / zoom, 1.2, 2.6)
    if (seg.hover || seg.isSel) ctx.setLineDash([5 / zoom, 3 / zoom])
    ctx.beginPath(); ctx.moveTo(seg.x0, seg.y); ctx.lineTo(seg.x1, seg.y); ctx.stroke()
    ctx.setLineDash([])
  }

  // Pass 2 – vertical segments with exactly ONE jumper per unique crossing Y
  for (const { pts, high, hover, isSel } of wirePolys) {
    for (let i = 0; i < pts.length - 1; i++) {
      const p0 = pts[i], p1 = pts[i + 1]
      if (Math.abs(p0.x - p1.x) > 0.5) continue // only vertical
      const x = p0.x
      const yMin = Math.min(p0.y, p1.y), yMax = Math.max(p0.y, p1.y)

      // Unique crossing Ys (rounded) where any horizontal covers this X
      const crossSet = new Map<number, number>() // roundedY → actual y
      for (const seg of hSegs) {
        if (seg.y <= yMin + 1 || seg.y >= yMax - 1) continue
        if (x < seg.x0 - 0.5 || x > seg.x1 + 0.5) continue
        const rk = Math.round(seg.y)
        if (!crossSet.has(rk)) crossSet.set(rk, seg.y)
      }
      const crosses = Array.from(crossSet.values()).sort((a, b) => a - b)

      const goingDown = p1.y > p0.y
      let cy = p0.y
      const rJump = 6 / zoom
      ctx.strokeStyle = isSel ? theme.sel : hover ? theme.wireHover : high ? theme.wireHigh : theme.wireLow
      ctx.lineWidth = isSel ? clamp(3 / zoom, 1.6, 3.4) : clamp(2.1 / zoom, 1.2, 2.6)
      if (hover || isSel) ctx.setLineDash([5 / zoom, 3 / zoom])
      for (const hy of crosses) {
        const pre = goingDown ? hy - rJump : hy + rJump
        ctx.beginPath(); ctx.moveTo(x, cy); ctx.lineTo(x, pre); ctx.stroke()
        // Single semicircle jumper (crocodile bridge)
        ctx.beginPath()
        ctx.arc(x, hy, rJump, goingDown ? -Math.PI / 2 : Math.PI / 2, goingDown ? Math.PI / 2 : -Math.PI / 2, false)
        ctx.stroke()
        cy = goingDown ? hy + rJump : hy - rJump
      }
      ctx.beginPath(); ctx.moveTo(x, cy); ctx.lineTo(x, p1.y); ctx.stroke()
      ctx.setLineDash([])
    }
  }

  // Waypoint handles
  for (const { w, isSel } of wirePolys) {
    if (!w.mids) continue
    w.mids.forEach((m, i) => {
      const midSel = selectedMids.has(`${w.id}:${i}`)
      const r = (midSel ? 6 : 4.5) / zoom
      ctx.beginPath(); ctx.arc(m.x, m.y, r, 0, Math.PI * 2)
      ctx.fillStyle = midSel ? theme.sel : theme.body
      ctx.fill()
      ctx.lineWidth = 1.4 / zoom
      ctx.strokeStyle = midSel ? theme.sel : (isSel ? theme.sel : theme.wireHover)
      ctx.stroke()
    })
  }

  // Nodes (with inline unfolded chips)
  for (const n of nodes) {
    if (n.kind === 'CHIP' && n.unfolded && n.chipId && chipById[n.chipId]) {
      drawUnfoldedChip(ctx, n, chipById[n.chipId], selected.has(n.id), signal, chipMeta, zoom, theme, dark)
      continue
    }
    drawNode(ctx, n, selected.has(n.id), signal, chipMeta, zoom, theme, dark)
  }
  // Pins on top
  for (const n of nodes) {
    for (const pin of enumeratePins(n))
      drawPin(ctx, pin.pos.x, pin.pos.y, !!signal[pinKey(pin.nodeId, pin.pinId)], zoom, theme)
  }

  if (pending) {
    const obstacles = nodes
      .filter((n) => n.id !== pending.start.nodeId)
      .map(inflatedBox)
    const pts = orthogonalPath(pending.startPos, pending.end, undefined, obstacles)
    ctx.strokeStyle = theme.wireHigh; ctx.setLineDash([5 / zoom, 4 / zoom]); ctx.lineWidth = 1.9 / zoom
    strokeWirePath(ctx, pts)
    ctx.stroke(); ctx.setLineDash([])
    ctx.beginPath(); ctx.arc(pending.end.x, pending.end.y, 3.8 / zoom, 0, Math.PI * 2)
    ctx.fillStyle = theme.wireHigh; ctx.fill()
  }

  if (placingNode) {
    drawNode(ctx, placingNode, false, {}, chipMeta, zoom, theme, dark, 0.62)
    for (const pin of enumeratePins(placingNode))
      drawPin(ctx, pin.pos.x, pin.pos.y, false, zoom, theme)
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
    ctx, w, h, scale, cam, nodes, wires, {}, new Set(), null, new Set(), null, new Set(),
    chipMeta, {}, null, null, null, theme, dark,
  )
  return { dataUrl: canvas.toDataURL('image/png'), width: w, height: h }
}

/* Persistence */
const STORAGE_KEY = 'logicmaker.v1'
interface SavedState {
  nodes: CircuitNode[]; wires: Wire[]; chips: ChipDefinition[]; camera: Camera; dark?: boolean
}
function loadState(): Partial<SavedState> {
  try { const raw = localStorage.getItem(STORAGE_KEY); return raw ? JSON.parse(raw) : {} } catch { return {} }
}
function saveState(s: SavedState) {
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify({ ...s, chips: s.chips.filter((c) => !c.builtin) }))
  } catch { /* */ }
}

/* Main */
type DragMode =
  | { kind: 'move'; ids: string[]; startWorld: Vec2; origin: Map<string, Vec2> }
  | { kind: 'box'; startX: number; startY: number; endX: number; endY: number }
  | { kind: 'wire'; start: PinRef; startPos: Vec2; end: Vec2 }
  | { kind: 'wireMid'; startWorld: Vec2; origins: Map<string, Vec2> }
  | null

export default function LogicMaker() {
  const saved = useMemo(() => loadState(), [])
  const [nodes, setNodes] = useState<CircuitNode[]>(saved.nodes ?? [])
  const [wires, setWires] = useState<Wire[]>(saved.wires ?? [])
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
  const [selectedMids, setSelectedMids] = useState<Set<string>>(new Set())
  const [ctxMenu, setCtxMenu] = useState<ContextMenuState | null>(null)
  const [paletteCtxMenu, setPaletteCtxMenu] = useState<{ x: number; y: number; placement: Placement } | null>(null)
  const [dark, setDark] = useState(saved.dark ?? false)
  const [, setFrameTick] = useState(0)

  const theme = dark ? DARK : LIGHT
  const canvasRef = useRef<HTMLCanvasElement>(null)
  const drag = useRef<DragMode>(null)
  const pan = useRef<{ startScreenX: number; startScreenY: number; startOffsetX: number; startOffsetY: number } | null>(null)
  const spaceDown = useRef(false)
  const pending = useRef<{ start: PinRef; startPos: Vec2 } | null>(null)
  const pendingDownScreen = useRef<{ x: number; y: number } | null>(null)
  const hoverWire = useRef<string | null>(null)
  const signal = useRef<SignalMap>({})
  const mousePos = useRef<Vec2>({ x: 0, y: 0 })
  const hasLoaded = useRef(false)
  const modalOpen = useRef(false)
  const buttonHeld = useRef<string | null>(null)

  const live = useRef({ nodes, wires, chips, selected, selectedWireId, selectedWireIds, placement, camera, selectedMids })
  useEffect(() => { live.current = { nodes, wires, chips, selected, selectedWireId, selectedWireIds, placement, camera, selectedMids } })
  useEffect(() => { modalOpen.current = !!(createModal || clockModal || renamePinModal || changeBlockModal) }, [createModal, clockModal, renamePinModal, changeBlockModal])

  const simulator = useMemo(() => new Simulator(), [])
  const chipsById = useMemo(() => Object.fromEntries(chips.map((c) => [c.id, c])), [chips])
  const compiled = useMemo(() => compileCircuit({ nodes, wires }, chipsById), [nodes, wires, chipsById])
  simulator.load(compiled)

  useEffect(() => {
    if (!hasLoaded.current) { hasLoaded.current = true; return }
    const t = setTimeout(() => saveState({ nodes, wires, chips, camera, dark }), 350)
    return () => clearTimeout(t)
  }, [nodes, wires, chips, camera, dark])

  useEffect(() => {
    const id = setInterval(() => {
      simulator.tick(live.current.nodes)
      signal.current = simulator.snapshot()
      setFrameTick((t) => (t + 1) % 1_000_000)
    }, 1000 / SIM_TPS)
    return () => clearInterval(id)
  }, [simulator])

  const pushHistory = useCallback(() => {
    setHistory((h) => {
      const entry = {
        nodes: live.current.nodes.map((n) => ({
          ...n, position: { ...n.position },
          inputs: n.inputs.map((p) => ({ ...p })),
          outputs: n.outputs.map((p) => ({ ...p })),
        })),
        wires: live.current.wires.map((w) => ({
          ...w,
          from: { ...w.from }, to: { ...w.to },
          mids: w.mids?.map((m) => ({ ...m })),
        })),
      }
      const next = [...h, entry]
      return next.length > 80 ? next.slice(-80) : next
    })
    setRedoStack([])
  }, [])

  const undo = useCallback(() => {
    setHistory((h) => {
      if (!h.length) return h
      const prev = h[h.length - 1]
      setRedoStack((r) => {
        const cur = {
          nodes: live.current.nodes.map((n) => ({ ...n, position: { ...n.position } })),
          wires: live.current.wires.map((w) => ({ ...w, mids: w.mids?.map((m) => ({ ...m })) })),
        }
        return [...r, cur].slice(-80)
      })
      setNodes(prev.nodes); setWires(prev.wires)
      setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setSelectedMids(new Set())
      return h.slice(0, -1)
    })
  }, [])

  const redo = useCallback(() => {
    setRedoStack((r) => {
      if (!r.length) return r
      const next = r[r.length - 1]
      setHistory((h) => {
        const cur = {
          nodes: live.current.nodes.map((n) => ({ ...n, position: { ...n.position } })),
          wires: live.current.wires.map((w) => ({ ...w, mids: w.mids?.map((m) => ({ ...m })) })),
        }
        return [...h, cur].slice(-80)
      })
      setNodes(next.nodes); setWires(next.wires)
      setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setSelectedMids(new Set())
      return r.slice(0, -1)
    })
  }, [])

  const canvasRect = () => canvasRef.current!.getBoundingClientRect()
  const screenToWorld = (sx: number, sy: number): Vec2 => {
    const c = live.current.camera
    return { x: (sx - c.offsetX) / c.zoom, y: (sy - c.offsetY) / c.zoom }
  }
  const posFromEvent = (e: React.PointerEvent | React.MouseEvent) => {
    const r = canvasRect()
    return screenToWorld(e.clientX - r.left, e.clientY - r.top)
  }

  const findPinAt = (p: Vec2) => {
    let best: EnumeratedPin | null = null, bestD = Infinity
    const grab = (PIN_R + 7) / live.current.camera.zoom
    for (const n of live.current.nodes)
      for (const pin of enumeratePins(n)) {
        const d = Math.hypot(p.x - pin.pos.x, p.y - pin.pos.y)
        if (d < grab && d < bestD) { bestD = d; best = pin }
      }
    return best
  }
  const findNodeAt = (p: Vec2) => {
    for (let i = live.current.nodes.length - 1; i >= 0; i--)
      if (hitNode(live.current.nodes[i], p)) return live.current.nodes[i]
    return null
  }
  const findMidAt = (p: Vec2): { wireId: string; midIndex: number } | null => {
    const grab = 12 / live.current.camera.zoom
    for (const w of live.current.wires) {
      if (!w.mids) continue
      for (let i = 0; i < w.mids.length; i++) {
        const d = Math.hypot(p.x - w.mids[i].x, p.y - w.mids[i].y)
        if (d < grab) return { wireId: w.id, midIndex: i }
      }
    }
    return null
  }
  const findHoveredWire = (p: Vec2) => {
    const zoom = live.current.camera.zoom
    const byId = new Map(live.current.nodes.map((n) => [n.id, n]))
    let best: string | null = null, bestD = 14 / zoom
    for (const w of live.current.wires) {
      const from = byId.get(w.from.nodeId), to = byId.get(w.to.nodeId)
      if (!from || !to) continue
      const vw = wireView(from, to, w)
      if (!vw) continue
      const pts = vw.pts
      for (let i = 0; i < pts.length - 1; i++) {
        const d = distToSegment(p, pts[i], pts[i + 1])
        if (d < bestD) { bestD = d; best = w.id }
      }
    }
    return best
  }

  /** Hit-test the collapse button in the top-right corner of an unfolded chip. */
  const findCollapseButton = (p: Vec2, n: CircuitNode): boolean => {
    if (!n.unfolded) return false
    const b = nodeBox(n)
    const btnW = 74, btnH = 18
    const bx = b.x + b.w - btnW - 8
    const by = b.y + 4
    return p.x >= bx && p.x <= bx + btnW && p.y >= by && p.y <= by + btnH
  }

  const place = (p: Vec2) => {
    if (!placement) return
    pushHistory()
    const ghostH = placement.type === 'PRIMITIVE'
      ? nodeHeight(createPrimitiveNode(placement.kind, { x: 0, y: 0 }))
      : 64
    const snapped = { x: snap(p.x - NODE_W_MIN / 2), y: snap(p.y - ghostH / 2) }
    let node: CircuitNode
    if (placement.type === 'CHIP') {
      const chip = chipsById[placement.chipId]
      if (!chip) return
      node = createChipNode(chip, snapped)
    } else {
      node = createPrimitiveNode(placement.kind, snapped)
    }
    setNodes((ns) => [...ns, node])
    setSelected(new Set([node.id]))
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
    setPlacement(null)
  }

  /** Batch-create N copies stacked vertically with compact spacing, centered at the cursor. */
  const batchCreate = (placement: Placement, count: number) => {
    if (!placement) { setPaletteCtxMenu(null); return }
    pushHistory()
    const cursor = mousePos.current
    // Compact gap ≈ component height + 20 px (snapped to grid)
    const sample =
      placement.type === 'PRIMITIVE'
        ? createPrimitiveNode(placement.kind, { x: 0, y: 0 })
        : (() => {
          const chip = chipsById[placement.chipId]
          return chip ? createChipNode(chip, { x: 0, y: 0 }) : null
        })()
    const ghostH = sample ? nodeHeight(sample) : 64
    const spacingY = snap(ghostH + 20)
    const newNodes: CircuitNode[] = []
    for (let i = 0; i < count; i++) {
      const pos = {
        x: snap(cursor.x - NODE_W_MIN / 2),
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
    if (e.button === 2) return

    const p = screenToWorld(sx, sy)
    canvasRef.current!.setPointerCapture(e.pointerId)

    if (placement) { place(p); return }

    const node = findNodeAt(p)

    // Collapse button on unfolded chip
    if (node && node.kind === 'CHIP' && node.unfolded && findCollapseButton(p, node)) {
      pushHistory()
      setNodes((ns) => ns.map((n) => n.id === node.id ? { ...n, unfolded: false, unfoldedSize: undefined } : n))
      return
    }

    if (node) {
      if (node.kind === 'INPUT') {
        const btnW = 44, btnH = 24
        const nw = nodeWidth(node)
        const bx = node.position.x + nw - btnW - 12
        const by = node.position.y + (nodeHeight(node) - btnH) / 2
        if (p.x >= bx && p.x <= bx + btnW && p.y >= by && p.y <= by + btnH) {
          pushHistory()
          setNodes((ns) => ns.map((n) => n.id === node.id ? { ...n, value: !n.value } : n))
          setSelected(new Set([node.id]))
          setSelectedWireId(null)
          setSelectedWireIds(new Set())
          return
        }
      }
      if (node.kind === 'BUTTON') {
        const btnW = 44, btnH = 24
        const nw = nodeWidth(node)
        const bx = node.position.x + nw - btnW - 12
        const by = node.position.y + (nodeHeight(node) - btnH) / 2
        if (p.x >= bx && p.x <= bx + btnW && p.y >= by && p.y <= by + btnH) {
          buttonHeld.current = node.id
          setNodes((ns) => ns.map((n) => n.id === node.id ? { ...n, value: true } : n))
          setSelected(new Set([node.id]))
          setSelectedWireId(null)
          setSelectedWireIds(new Set())
          return
        }
      }
      if (node.kind === 'CLOCK') {
        // Left-click on the embedded ON/OFF button toggles pulse generation
        const btnW = 44, btnH = 24
        const nw = nodeWidth(node)
        const bx = node.position.x + nw - btnW - 12
        const by = node.position.y + (nodeHeight(node) - btnH) / 2
        if (p.x >= bx && p.x <= bx + btnW && p.y >= by && p.y <= by + btnH) {
          pushHistory()
          setNodes((ns) => ns.map((n) => n.id === node.id ? { ...n, enabled: n.enabled === false ? true : false } : n))
          setSelected(new Set([node.id]))
          setSelectedWireId(null)
          setSelectedWireIds(new Set())
          return
        }
        // Body click falls through → normal drag / select (no modal on single click)
      }
    }

    const pin = findPinAt(p)
    if (pin) {
      if (pending.current && !drag.current) {
        const start = pending.current.start
        const end: PinRef = { nodeId: pin.nodeId, pinId: pin.pinId, side: pin.side }
        if (tryFinishWire(start, end)) {
          pending.current = null
          drag.current = null
          pendingDownScreen.current = null
          return
        }
      }
      pending.current = { start: { nodeId: pin.nodeId, pinId: pin.pinId, side: pin.side }, startPos: pin.pos }
      pendingDownScreen.current = { x: sx, y: sy }
      return
    }

    if (pending.current && !pin) {
      pending.current = null
      pendingDownScreen.current = null
      return
    }

    if (node) {
      const multi = e.shiftKey || selected.has(node.id)
      const next = new Set<string>(multi ? selected : [])
      next.add(node.id)
      setSelected(next)
      setSelectedWireId(null)
      setSelectedWireIds(new Set())
      setSelectedMids(new Set())
      const origin = new Map<string, Vec2>()
      for (const n of live.current.nodes) if (next.has(n.id)) origin.set(n.id, { ...n.position })
      drag.current = { kind: 'move', ids: Array.from(next), startWorld: p, origin }
      return
    }

    const mid = findMidAt(p)
    if (mid) {
      const key = `${mid.wireId}:${mid.midIndex}`
      setSelected(new Set())
      setSelectedWireId(null)
      setSelectedWireIds(new Set())
      let nextMids: Set<string>
      if (e.shiftKey) {
        nextMids = new Set(selectedMids)
        if (nextMids.has(key)) nextMids.delete(key)
        else nextMids.add(key)
      } else if (selectedMids.has(key) && selectedMids.size > 1) {
        nextMids = selectedMids
      } else {
        nextMids = new Set([key])
      }
      setSelectedMids(nextMids)
      const origins = new Map<string, Vec2>()
      for (const w of live.current.wires) {
        if (!w.mids) continue
        w.mids.forEach((m, i) => {
          const k = `${w.id}:${i}`
          if (nextMids.has(k)) origins.set(k, { ...m })
        })
      }
      drag.current = { kind: 'wireMid', startWorld: p, origins }
      return
    }

    const hw = findHoveredWire(p)
    if (hw && e.detail >= 2) {
      pushHistory()
      const byId = new Map(live.current.nodes.map((n) => [n.id, n]))
      setWires((ws) => ws.map((w) => {
        if (w.id !== hw) return w
        const from = byId.get(w.from.nodeId), to = byId.get(w.to.nodeId)
        if (!from || !to) return w
        const vw = wireView(from, to, w)
        if (!vw) return w
        const mids = insertMidAtClick(vw.pts, w.mids, p)
        return { ...w, mids }
      }))
      setSelectedWireId(hw)
      setSelectedWireIds(new Set())
      setSelected(new Set())
      setSelectedMids(new Set())
      return
    }
    if (hw) {
      setSelectedWireId(hw)
      setSelectedWireIds(new Set())
      setSelected(new Set())
      setSelectedMids(new Set())
      return
    }

    setSelected(new Set())
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
    setSelectedMids(new Set())
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

    if (pending.current && !drag.current && pendingDownScreen.current) {
      const dx = sx - pendingDownScreen.current.x, dy = sy - pendingDownScreen.current.y
      if (Math.hypot(dx, dy) > 6) {
        drag.current = { kind: 'wire', start: pending.current.start, startPos: pending.current.startPos, end: p }
      }
    }

    if (drag.current?.kind === 'box') { drag.current.endX = p.x; drag.current.endY = p.y }
    else if (drag.current?.kind === 'wire') drag.current.end = p
    else if (drag.current?.kind === 'wireMid') {
      const d = drag.current
      const dx = p.x - d.startWorld.x
      const dy = p.y - d.startWorld.y
      // Update live wires immediately so the RAF loop draws without lag
      const nextWires = live.current.wires.map((w) => {
        if (!w.mids) return w
        let changed = false
        const mids = w.mids.map((m, i) => {
          const k = `${w.id}:${i}`
          const origin = d.origins.get(k)
          if (!origin) return m
          changed = true
          return { x: origin.x + dx, y: origin.y + dy }
        })
        return changed ? { ...w, mids } : w
      })
      live.current.wires = nextWires
      setWires(nextWires)
    } else if (drag.current?.kind === 'move') {
      const d = drag.current, dx = p.x - d.startWorld.x, dy = p.y - d.startWorld.y
      const idSet = new Set(d.ids)
      // Keep pins glued to the component body in real time (no post-drop lag)
      const nextNodes = live.current.nodes.map((n) => idSet.has(n.id)
        ? { ...n, position: { x: d.origin.get(n.id)!.x + dx, y: d.origin.get(n.id)!.y + dy } }
        : n)
      live.current.nodes = nextNodes
      setNodes(nextNodes)
    } else hoverWire.current = findHoveredWire(p)
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
    const p = posFromEvent(e)
    const d = drag.current

    if (d?.kind === 'wire') {
      const pinHit = findPinAt(p)
      if (pinHit) {
        const start = d.start
        const end: PinRef = { nodeId: pinHit.nodeId, pinId: pinHit.pinId, side: pinHit.side }
        tryFinishWire(start, end)
      }
      pending.current = null
      pendingDownScreen.current = null
      drag.current = null
      return
    }

    if (d?.kind === 'box') {
      const minX = Math.min(d.startX, d.endX), maxX = Math.max(d.startX, d.endX)
      const minY = Math.min(d.startY, d.endY), maxY = Math.max(d.startY, d.endY)
      const next = new Set<string>()
      for (const n of live.current.nodes) {
        const b = nodeBox(n)
        if (b.x < maxX && b.x + b.w > minX && b.y < maxY && b.y + b.h > minY) next.add(n.id)
      }
      setSelected(next)
      const midKeys = new Set<string>()
      for (const w of live.current.wires) {
        if (!w.mids) continue
        w.mids.forEach((m, i) => {
          if (m.x >= minX && m.x <= maxX && m.y >= minY && m.y <= maxY) {
            midKeys.add(`${w.id}:${i}`)
          }
        })
      }
      setSelectedMids(midKeys)
      const byId = new Map(live.current.nodes.map((n) => [n.id, n]))
      const wireIds = new Set<string>()
      for (const w of live.current.wires) {
        const from = byId.get(w.from.nodeId), to = byId.get(w.to.nodeId)
        if (!from || !to) continue
        const vw = wireView(from, to, w)
        if (!vw) continue
        const inside = vw.pts.some((pt) => pt.x >= minX && pt.x <= maxX && pt.y >= minY && pt.y <= maxY)
        if (inside) wireIds.add(w.id)
      }
      setSelectedWireIds(wireIds)
      if (midKeys.size || wireIds.size) setSelectedWireId(null)
    } else if (d?.kind === 'wireMid') {
      pushHistory()
    } else if (d?.kind === 'move') {
      const idSet = new Set(d.ids)
      setNodes((ns) => ns.map((n) => idSet.has(n.id)
        ? { ...n, position: { x: snap(n.position.x), y: snap(n.position.y) } } : n))
      // After realignment, drop waypoints that have become collinear (auto-merge straight wires)
      setWires((ws) => {
        const byId = new Map(live.current.nodes.map((n) => [n.id, n]))
        // Use the just-snapped positions
        for (const n of live.current.nodes) {
          if (idSet.has(n.id)) byId.set(n.id, { ...n, position: { x: snap(n.position.x), y: snap(n.position.y) } })
        }
        return ws.map((w) => {
          if (!w.mids?.length) return w
          if (!idSet.has(w.from.nodeId) && !idSet.has(w.to.nodeId)) return w
          const from = byId.get(w.from.nodeId), to = byId.get(w.to.nodeId)
          if (!from || !to) return w
          const a = pinAnchor(from, w.from), b = pinAnchor(to, w.to)
          if (!a || !b) return w
          // Rebuild path with current mids; if the simplified path has no interior bends that match mids, clear them
          const pts = orthogonalPath(a, b, w.mids)
          // If path collapsed to ≤ 3 points (simple L or straight), drop explicit mids
          if (pts.length <= 3) return { ...w, mids: undefined }
          return w
        })
      })
    }
    drag.current = null
  }

  /** Attempt to create a wire. Enforces strict Output→Input pin rules. */
  const tryFinishWire = (a: PinRef, b: PinRef): boolean => {
    if (isPinRefEqual(a, b)) return false
    if (a.nodeId === b.nodeId) return false
    // Strict: only OUT → IN allowed
    if (a.side === 'out' && b.side === 'in') return finishWire(a, b)
    if (a.side === 'in' && b.side === 'out') return finishWire(b, a)
    // Input→Input or Output→Output — reject silently
    return false
  }
  const finishWire = (from: PinRef, to: PinRef): boolean => {
    if (from.side !== 'out' || to.side !== 'in') return false
    pushHistory()
    setWires((ws) => [...ws.filter((w) => !(w.to.side === 'in' && isPinRefEqual(w.to, to))), createWire(from, to)])
    return true
  }

  /** Delete every currently-selected item in a single action:
   *  nodes (with their attached wires), wires, waypoints, and mixed selections. */
  const deleteSelection = () => {
    const mids = live.current.selectedMids
    const boxWires = live.current.selectedWireIds
    const wireId = live.current.selectedWireId
    const ids = live.current.selected
    if (!mids.size && !boxWires.size && !wireId && !ids.size) return

    pushHistory()

    // 1) Remove specific waypoints
    if (mids.size > 0) {
      setWires((ws) => ws.map((w) => {
        if (!w.mids) return w
        const keep = w.mids.filter((_, i) => !mids.has(`${w.id}:${i}`))
        return { ...w, mids: keep.length ? keep : undefined }
      }))
    }

    // 2) Remove whole wires that were selected
    const wiresToDelete = new Set(boxWires)
    if (wireId) wiresToDelete.add(wireId)

    // 3) Remove nodes and any wire attached to them (both ends)
    setNodes((ns) => ns.filter((n) => !ids.has(n.id)))
    setWires((ws) => ws.filter((w) => {
      if (wiresToDelete.has(w.id)) return false
      if (ids.has(w.from.nodeId) || ids.has(w.to.nodeId)) return false
      return true
    }))

    setSelected(new Set())
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
    setSelectedMids(new Set())
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
          mids: w.mids?.map((m) => ({ ...m })),
        })),
    })
  }
  const cutSelection = () => { copySelection(); deleteSelection() }
  const pasteClipboard = () => {
    const clip = clipboard
    if (!clip?.nodes.length) return
    pushHistory()
    const idMap = new Map<string, string>()
    const offset = 20 // +20px offset per spec
    const newNodes = clip.nodes.map((n) => {
      const newId = uid(n.kind.toLowerCase())
      idMap.set(n.id, newId)
      return {
        ...n,
        id: newId,
        position: { x: n.position.x + offset, y: n.position.y + offset },
        inputs: n.inputs.map((p) => ({ ...p })),
        outputs: n.outputs.map((p) => ({ ...p })),
      }
    })
    const newWires = clip.wires.map((w) => ({
      id: uid('w'),
      from: { ...w.from, nodeId: idMap.get(w.from.nodeId)! },
      to: { ...w.to, nodeId: idMap.get(w.to.nodeId)! },
      mids: w.mids?.map((m) => ({ x: m.x + offset, y: m.y + offset })),
    }))
    setNodes((ns) => [...ns, ...newNodes])
    setWires((ws) => [...ws, ...newWires])
    setSelected(new Set(newNodes.map((n) => n.id)))
    setSelectedWireId(null)
    setSelectedWireIds(new Set())
    setSelectedMids(new Set())
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

  /** Compute the bounding size for an unfolded chip and apply it to a node. */
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
    const pad = 40
    const header = 28
    // Generous padding keeps the unfolded dashed container from clipping adjacent nodes
    const w = Math.max(260, (maxX - minX) + pad * 2)
    const h = Math.max(140, (maxY - minY) + pad * 2 + header)
    pushHistory()
    setNodes((ns) => ns.map((n) => n.id === nodeId
      ? { ...n, unfolded: true, unfoldedSize: { w, h } }
      : n))
  }
  const foldChip = (nodeId: string) => {
    pushHistory()
    setNodes((ns) => ns.map((n) => n.id === nodeId
      ? { ...n, unfolded: false, unfoldedSize: undefined }
      : n))
  }

  const enterEditChip = (chipId: string) => {
    if (editing) return
    const chip = chipsById[chipId]
    if (!chip || chip.builtin) return
    setCtxMenu(null)
    setEditing({
      chipId, snapNodes: live.current.nodes, snapWires: live.current.wires,
      snapSelected: live.current.selected, snapCamera: live.current.camera,
    })
    const mapped = chip.nodes.map((n) => ({ ...n, position: { ...n.position } }))
    setNodes(mapped)
    setWires(chip.wires.map((w) => ({ ...w })))
    setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setPlacement(null); pending.current = null
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
      } else {
        setNodes(session.snapNodes); setWires(session.snapWires)
      }
      setSelected(session.snapSelected); setSelectedWireId(null); setSelectedWireIds(new Set()); setCamera(session.snapCamera)
      setPlacement(null); pending.current = null
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

  /** Instant component swap / morph. Remaps wires by pin *index* (primary first)
   *  so AND→NOT keeps the first input, drops the second; NOT→AND keeps the single
   *  input on pin 0 and leaves pin 1 free. Labels and values are preserved when possible. */
  const replaceNodeKind = (nodeId: string, newKind: PrimitiveType) => {
    applyNodeReplacement(nodeId, { type: 'PRIMITIVE', kind: newKind })
  }

  /** General replacement used by both the quick gate menu and the Change Block modal. */
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
      // Always reset to the default name of the new block (never keep a custom-chip label)
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
    if (placement) return
    const p = screenToWorld(e.clientX - canvasRect().left, e.clientY - canvasRect().top)
    if (findMidAt(p)) return
    const hw = findHoveredWire(p)
    if (hw) {
      pushHistory()
      const byId = new Map(live.current.nodes.map((n) => [n.id, n]))
      setWires((ws) => ws.map((w) => {
        if (w.id !== hw) return w
        const from = byId.get(w.from.nodeId), to = byId.get(w.to.nodeId)
        if (!from || !to) return w
        const vw = wireView(from, to, w)
        if (!vw) return w
        const mids = insertMidAtClick(vw.pts, w.mids, p)
        return { ...w, mids }
      }))
      setSelectedWireId(hw)
      setSelectedWireIds(new Set())
      setSelected(new Set())
      setSelectedMids(new Set())
      return
    }
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
      // Double-click CLK body or button → frequency settings
      setClockModal({ id: node.id, period: node.period ?? 30 })
      setSelected(new Set([node.id]))
      setSelectedWireId(null)
      setSelectedWireIds(new Set())
      return
    }
    if (node?.kind === 'CHIP' && node.chipId) {
      // Double-click a custom chip instance toggles inline unfold
      if (!chipsById[node.chipId]?.builtin) {
        if (node.unfolded) foldChip(node.id)
        else unfoldChip(node.id)
      }
    }
  }

  const onContextMenu = (e: React.MouseEvent) => {
    e.preventDefault()
    const p = posFromEvent(e)
    const node = findNodeAt(p)
    const wireId = findHoveredWire(p)
    const midHit = findMidAt(p)

    let target: ContextMenuState['target'] = 'canvas'
    let nodeId: string | undefined, wId: string | undefined, waypointIndex: number | undefined

    if (midHit) {
      target = 'waypoint'
      wId = midHit.wireId
      waypointIndex = midHit.midIndex
      setSelectedWireId(midHit.wireId); setSelected(new Set()); setSelectedWireIds(new Set())
      setSelectedMids(new Set([`${midHit.wireId}:${midHit.midIndex}`]))
    } else if (node) {
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
    setCtxMenu({ x: e.clientX, y: e.clientY, world: p, target, nodeId, wireId: wId, waypointIndex })
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
        setSelectedWireId(null)
      } else {
        deleteSelection()
      }
    } else if (action === 'deleteWaypoint' && wireId != null && ctxMenu.waypointIndex != null) {
      pushHistory()
      const idx = ctxMenu.waypointIndex
      setWires((ws) => ws.map((w) => {
        if (w.id !== wireId || !w.mids) return w
        const keep = w.mids.filter((_, i) => i !== idx)
        return { ...w, mids: keep.length ? keep : undefined }
      }))
      setSelectedMids(new Set())
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
    } else if (action === 'addPoint' && wireId) {
      pushHistory()
      const pt = ctxMenu.world
      const byId = new Map(live.current.nodes.map((n) => [n.id, n]))
      setWires((ws) => ws.map((x) => {
        if (x.id !== wireId) return x
        const from = byId.get(x.from.nodeId), to = byId.get(x.to.nodeId)
        if (!from || !to) return { ...x, mids: [...(x.mids ?? []), pt] }
        const vw = wireView(from, to, x)
        if (!vw) return { ...x, mids: [...(x.mids ?? []), pt] }
        return { ...x, mids: insertMidAtClick(vw.pts, x.mids, pt) }
      }))
    } else if (action === 'clearMids' && wireId) {
      pushHistory()
      setWires((ws) => ws.map((w) => w.id === wireId ? { ...w, mids: undefined } : w))
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
    setNodes([]); setWires([]); setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setPlacement(null)
    pending.current = null; simulator.reset(); signal.current = {}
  }

  const exportJSON = () => {
    const data = { version: 1, nodes, wires, chips: chips.filter((c) => !c.builtin), camera, dark }
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
        setNodes(data.nodes); setWires(data.wires)
        setChips([...makeBuiltInChips(), ...(data.chips ?? [])])
        if (data.camera) setCamera(data.camera)
        if (typeof data.dark === 'boolean') setDark(data.dark)
        setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setPlacement(null); pending.current = null
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

  // Keep latest handlers accessible from the keydown effect (fixes stale Ctrl+V etc.)
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
      // Use e.code (physical key) so shortcuts keep working regardless of active layout
      if (mod && e.code === 'KeyZ' && !e.shiftKey) { e.preventDefault(); actionsRef.current.undo(); return }
      if (mod && (e.code === 'KeyY' || (e.code === 'KeyZ' && e.shiftKey))) { e.preventDefault(); actionsRef.current.redo(); return }
      if (mod && e.code === 'KeyC') { e.preventDefault(); actionsRef.current.copySelection(); return }
      if (mod && e.code === 'KeyV') { e.preventDefault(); actionsRef.current.pasteClipboard(); return }
      if (mod && e.code === 'KeyX') { e.preventDefault(); actionsRef.current.cutSelection(); return }
      if (e.key === 'Escape') {
        pending.current = null; pendingDownScreen.current = null; setPlacement(null); setCreateModal(false)
        setClockModal(null); setRenamePinModal(null); setChangeBlockModal(null); setCtxMenu(null); setPaletteCtxMenu(null)
        setSelected(new Set()); setSelectedWireId(null); setSelectedWireIds(new Set()); setSelectedMids(new Set())
      }
      if ((e.key === 'Delete' || e.key === 'Backspace')
        && (live.current.selected.size > 0
          || live.current.selectedWireId
          || live.current.selectedWireIds.size > 0
          || live.current.selectedMids.size > 0)) {
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
      let pnd: { start: PinRef; startPos: Vec2; end: Vec2 } | null = null
      if (drag.current?.kind === 'wire')
        pnd = { start: drag.current.start, startPos: drag.current.startPos, end: drag.current.end }
      else if (pending.current)
        pnd = { start: pending.current.start, startPos: pending.current.startPos, end: mousePos.current }

      const chipMeta: Record<string, { color: string }> = {}
      for (const c of s.chips) chipMeta[c.id] = { color: c.color }
      const chipById: Record<string, ChipDefinition> = {}
      for (const c of s.chips) chipById[c.id] = c

      let placingNode: CircuitNode | null = null
      if (s.placement) {
        if (s.placement.type === 'CHIP') {
          const chip = s.chips.find((c) => c.id === s.placement!.chipId)
          if (chip) {
            const h = nodeHeight(createChipNode(chip, { x: 0, y: 0 }))
            placingNode = createChipNode(chip, {
              x: snap(mousePos.current.x - NODE_W_MIN / 2),
              y: snap(mousePos.current.y - h / 2),
            })
          }
        } else {
          const h = nodeHeight(createPrimitiveNode(s.placement.kind, { x: 0, y: 0 }))
          placingNode = createPrimitiveNode(s.placement.kind, {
            x: snap(mousePos.current.x - NODE_W_MIN / 2),
            y: snap(mousePos.current.y - h / 2),
          })
        }
      }

      drawScene(ctx, cw, ch, dpr, s.camera, s.nodes, s.wires, signal.current,
        s.selected, s.selectedWireId, s.selectedWireIds, hoverWire.current, s.selectedMids,
        chipMeta, chipById, pnd, box, placingNode, theme, dark)
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

  /** Smart viewport-aware placement for context / palette menus.
   *  Flips upward or leftward when near screen edges so the popup stays fully visible. */
  const clampMenuPos = (clientX: number, clientY: number, estimatedW: number, estimatedH: number) => {
    const pad = 8
    let left = clientX
    let top = clientY
    if (left + estimatedW > window.innerWidth - pad) {
      left = Math.max(pad, clientX - estimatedW)
    }
    if (top + estimatedH > window.innerHeight - pad) {
      top = Math.max(pad, clientY - estimatedH)
    }
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
            {(['INPUT', 'OUTPUT', 'CLOCK', 'BUTTON'] as PrimitiveType[]).map((k) => (
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
            {(['AND', 'OR', 'NOT'] as PrimitiveType[]).map((k) => (
              <button key={k} onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
                onContextMenu={(e) => { e.preventDefault(); setPaletteCtxMenu({ x: e.clientX, y: e.clientY, placement: { type: 'PRIMITIVE', kind: k } }) }}
                className={`${btn} ${isPrim(k) ? active : idle}`}>
                <span className={`grid h-7 w-7 place-items-center rounded text-sm font-bold ring-1 ${dark ? 'bg-slate-700 ring-slate-600' : 'bg-slate-100 ring-slate-200'}`}
                  style={{ color: GATE_EDGE[k] }}>
                  {k === 'AND' ? '∧' : k === 'OR' ? '∨' : '¬'}
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
                      onClick={(e) => {
                        e.stopPropagation()
                        enterEditChip(c.id)
                      }}
                      onKeyDown={(e) => {
                        if (e.key === 'Enter' || e.key === ' ') {
                          e.stopPropagation()
                          enterEditChip(c.id)
                        }
                      }}
                      className={`absolute right-0.5 top-0.5 z-10 grid h-4 w-4 place-items-center rounded-full shadow ring-1 ${dark ? 'bg-slate-800 text-slate-200 ring-slate-600 hover:bg-slate-700' : 'bg-white text-slate-600 ring-slate-300 hover:bg-slate-50'}`}
                      title="Edit"
                    >
                      <Pencil size={10} />
                    </span>
                    <button
                      type="button"
                      onClick={() => setPlacement({ type: 'CHIP', chipId: c.id })}
                      onContextMenu={(e) => {
                        e.preventDefault()
                        setPaletteCtxMenu({ x: e.clientX, y: e.clientY, placement: { type: 'CHIP', chipId: c.id } })
                      }}
                      className={`${btn} ${isChip(c.id) ? active : idle}`}
                    >
                      <span
                        className={`grid h-7 min-w-7 place-items-center rounded px-1 text-xs font-bold ring-1 ${dark ? 'bg-slate-700' : 'bg-slate-100'}`}
                        style={{ color: c.color, borderColor: c.color + '66' }}
                      >
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
          style={clampMenuPos(ctxMenu.x, ctxMenu.y, 240, ctxMenu.target === 'waypoint' ? 80 : 360)}
          onMouseLeave={() => setCtxMenu(null)}
        >
          {ctxMenu.target === 'waypoint' ? (
            <>
              <button className={menuItemCls} onClick={() => ctxAction('deleteWaypoint')}>
                <Trash2 size={14} /> Delete waypoint
              </button>
              <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
              <button className={menuItemCls} onClick={() => ctxAction('clearMids')}>
                Clear all waypoints
              </button>
            </>
          ) : ctxMenu.target === 'wire' ? (
            <>
              <button className={menuItemCls} onClick={() => ctxAction('addPoint')}>
                <Pencil size={14} /> Add waypoint
              </button>
              <button className={menuItemCls} onClick={() => ctxAction('clearMids')}>
                Clear waypoints
              </button>
              <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
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
          <div className={`w-72 max-h-[70vh] overflow-y-auto rounded-xl border p-4 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}>
            <h2 className="mb-1 text-sm font-semibold">Change Block</h2>
            <p className="mb-3 text-[11px] opacity-60">Wires are re-mapped by pin index. Label resets to the new default.</p>
            {/* Single vertical list: standard gates first, then chips */}
            <div className="flex flex-col gap-0.5">
              {(['AND', 'OR', 'NOT', 'INPUT', 'OUTPUT', 'CLOCK', 'BUTTON'] as PrimitiveType[]).map((k) => (
                <button
                  key={k}
                  className={menuItemCls}
                  onClick={() => applyNodeReplacement(changeBlockModal.nodeId, { type: 'PRIMITIVE', kind: k })}
                >
                  <span
                    className="inline-block h-2.5 w-2.5 rounded-sm"
                    style={{ background: GATE_EDGE[k] }}
                  />
                  {k}
                </button>
              ))}
              {[...builtinChips, ...customChips].length > 0 && (
                <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
              )}
              {[...builtinChips, ...customChips].map((c) => (
                <button
                  key={c.id}
                  className={menuItemCls}
                  onClick={() => applyNodeReplacement(changeBlockModal.nodeId, { type: 'CHIP', chipId: c.id })}
                >
                  <span className="inline-block h-2.5 w-2.5 rounded-full" style={{ background: c.color }} />
                  {c.name}
                </button>
              ))}
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