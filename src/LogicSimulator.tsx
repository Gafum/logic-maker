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
  Palette,
  Type,
  Timer,
  Circle,
  Lightbulb,
  RotateCw,
  Crosshair,
  FileText,
  Link2,
  MousePointer2,
} from 'lucide-react'

/* =====================================================================
 *  LogicMaker — clean rewrite
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
  /** Rotation in degrees: 0 | 90 | 180 | 270 */
  rotation?: 0 | 90 | 180 | 270
}
interface Wire {
  id: string
  from: PinRef
  to: PinRef
  /** optional routing control points the path must pass through */
  mids?: Vec2[]
  /**
   * Path style:
   * - false / undefined = smooth cubic Bézier through anchors (default)
   * - true = straight polyline point-to-point (no curves)
   */
  straight?: boolean
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
  target: 'canvas' | 'node' | 'wire' | 'chip'
  nodeId?: string
  wireId?: string
}

const pinKey = (n: string, p: string) => `${n}:${p}`
const isPinRefEqual = (a: PinRef, b: PinRef) =>
  a.nodeId === b.nodeId && a.pinId === b.pinId && a.side === b.side

/* Geometry */
const GRID = 24
const NODE_W_MIN = 110
const NODE_PAD = 14
const PIN_SPACING = 26
const PIN_R = 5.5
const MIN_ZOOM = 0.05
const MAX_ZOOM = 4

let idCounter = 0
const uid = (prefix = 'n') =>
  `${prefix}_${(idCounter++).toString(36)}_${Math.random().toString(36).slice(2, 6)}`
const clamp = (v: number, lo: number, hi: number) => Math.min(hi, Math.max(lo, v))
const snap = (v: number) => Math.round(v / GRID) * GRID

/** Approximate text width for dynamic node sizing (UI font ~12px medium) */
function approxLabelWidth(label: string): number {
  // rough avg char width for ui-sans-serif 12px bold/medium
  return Math.ceil(label.length * 7.2) + 28
}

const nodeRows = (n: CircuitNode) => Math.max(n.inputs.length, n.outputs.length, 1)
const nodeHeight = (n: CircuitNode) =>
  NODE_PAD * 2 + PIN_SPACING * Math.max(nodeRows(n) - 1, 0) + PIN_SPACING
const nodeWidth = (n: CircuitNode) => {
  const base = NODE_W_MIN
  const fromLabel = approxLabelWidth(n.label)
  // chips / gates may have long pin names too
  let pinExtra = 0
  if (n.kind === 'CHIP') {
    const longest = Math.max(
      0,
      ...n.inputs.map((p) => p.name.length),
      ...n.outputs.map((p) => p.name.length),
    )
    pinExtra = Math.max(0, longest * 6 - 20)
  }
  return Math.max(base, fromLabel, NODE_W_MIN + pinExtra)
}
const nodeBox = (n: CircuitNode) => ({
  x: n.position.x, y: n.position.y, w: nodeWidth(n), h: nodeHeight(n),
})
/** Evenly distribute pins across full node height; a single pin is centered. */
function pinY(n: CircuitNode, index: number, count: number): number {
  const h = nodeHeight(n)
  if (count <= 1) return n.position.y + h / 2
  const top = n.position.y + NODE_PAD + PIN_SPACING / 2
  const bot = n.position.y + h - NODE_PAD - PIN_SPACING / 2
  return top + ((bot - top) * index) / (count - 1)
}
const leftPinPos = (n: CircuitNode, i: number): Vec2 => ({
  x: n.position.x,
  y: pinY(n, i, n.inputs.length),
})
const rightPinPos = (n: CircuitNode, i: number): Vec2 => ({
  x: n.position.x + nodeWidth(n),
  y: pinY(n, i, n.outputs.length),
})

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

/* ---- colour helpers: derive solid tinted fills instead of alpha-transparency ---- */
function hexToRgb(hex: string) {
  const h = hex.replace('#', '')
  const full = h.length === 3 ? h.split('').map((c) => c + c).join('') : h
  const num = parseInt(full, 16)
  return { r: (num >> 16) & 255, g: (num >> 8) & 255, b: num & 255 }
}
/** amount > 0 lightens toward white, amount < 0 darkens toward black */
function shade(hex: string, amount: number) {
  const { r, g, b } = hexToRgb(hex)
  const t = amount >= 0 ? 255 : 0
  const p = Math.min(1, Math.abs(amount))
  const mix = (c: number) => Math.round(c + (t - c) * p)
  return `rgb(${mix(r)}, ${mix(g)}, ${mix(b)})`
}
/** solid (non-transparent) fill for a gate/chip body, tuned per theme */
function solidFill(edgeColor: string | undefined, dark: boolean, fallback: string) {
  if (!edgeColor) return fallback
  return dark ? shade(edgeColor, -0.72) : shade(edgeColor, 0.86)
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
    ...(kind === 'CLOCK' ? { period: 30, value: false } : {}),
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
          const period = Math.max(2, n.period ?? 30)
          const half = Math.floor(period / 2)
          this.state.set(net, (this.tickCount % period) < half)
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
  bg: '#111111', grid: '#1c1c1c', wireHigh: '#38bdf8', wireLow: '#3f3f46', wireHover: '#52525b',
  pinHigh: '#38bdf8', pinLow: '#3f3f46', body: '#1a1a1a', edge: '#71717a', label: '#e4e4e7', sel: '#38bdf8',
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

/** Anchor points for a wire: start, optional user control points, end. */
function wireAnchors(a: Vec2, b: Vec2, mids?: Vec2[]): Vec2[] {
  if (mids?.length) return [a, ...mids, b]
  return [a, b]
}

/** Project point P onto segment AB; returns closest point + distance + t in [0,1]. */
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

/**
 * Insert a control point into a wire at the correct segment index so the path
 * order stays left-to-right along the wire (not always appended at the end).
 */
function insertMidAtClick(
  anchors: Vec2[], // [start, ...mids, end]
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
      bestPoint = proj.point // sits exactly on the segment the user hovered
    }
  }
  // anchors = [start, mid0, mid1, ..., end]
  // segment i is between anchors[i] and anchors[i+1]
  // → new mid goes into mids at index `bestSeg`
  mids.splice(bestSeg, 0, bestPoint)
  return mids
}

function drawBody(
  ctx: CanvasRenderingContext2D, n: CircuitNode,
  fill: string, edge: string | null,
  selected: boolean, zoom: number, theme: Theme,
) {
  const b = nodeBox(n)
  if (selected) {
    ctx.save()
    ctx.strokeStyle = theme.sel
    ctx.lineWidth = 2.8 / zoom
    roundRect(ctx, b.x - 3.5, b.y - 3.5, b.w + 7, b.h + 7, 10)
    ctx.stroke(); ctx.restore()
  }
  ctx.fillStyle = fill
  roundRect(ctx, b.x, b.y, b.w, b.h, 8); ctx.fill()
  ctx.strokeStyle = edge ?? theme.edge
  ctx.lineWidth = 1.6
  roundRect(ctx, b.x, b.y, b.w, b.h, 8); ctx.stroke()
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
      ? !!signal[pinKey(n.id, 'out')]
      : !!n.value
    const btnW = 44, btnH = 24
    const nw = nodeWidth(n)
    const bx = n.position.x + nw - btnW - 12
    const by = n.position.y + (b.h - btnH) / 2
    ctx.fillStyle = value ? theme.wireHigh : (dark ? '#334155' : '#e2e8f0')
    roundRect(ctx, bx, by, btnW, btnH, 6); ctx.fill()
    ctx.strokeStyle = value ? theme.wireHigh : theme.pinLow; ctx.lineWidth = 1.2; ctx.stroke()
    ctx.fillStyle = value ? '#fff' : theme.label
    ctx.font = '700 10px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle'
    const txt = n.kind === 'CLOCK'
      ? `${(60 / Math.max(2, n.period ?? 30)).toFixed(1)}Hz`
      : n.kind === 'BUTTON' ? (value ? 'HOLD' : 'BTN')
        : (value ? 'ON' : 'OFF')
    ctx.fillText(txt, bx + btnW / 2, by + btnH / 2 + 0.5)
    ctx.fillStyle = theme.label
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'left'
    ctx.fillText(n.label, n.position.x + 12, n.position.y + b.h / 2)
    ctx.restore()
    return
  }

  if (n.kind === 'OUTPUT') {
    drawBody(ctx, n, fill, edge, selected, zoom, theme)
    const value = !!signal[pinKey(n.id, n.inputs[0]?.id ?? 'in')]
    const nw = nodeWidth(n)
    const cy = leftPinPos(n, 0).y, cx = n.position.x + nw - 28
    if (value) { ctx.save(); ctx.shadowColor = theme.wireHigh + '80'; ctx.shadowBlur = 14 }
    // Classic lightbulb-style indicator
    ctx.beginPath()
    ctx.arc(cx, cy - 2, 9, 0, Math.PI * 2)
    ctx.fillStyle = value ? theme.wireHigh : (dark ? '#334155' : '#cbd5e1'); ctx.fill()
    ctx.strokeStyle = value ? theme.wireHigh : theme.pinLow; ctx.lineWidth = 1.5; ctx.stroke()
    // base of bulb
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
    ctx.fillText(n.label, n.position.x + 12, cy)
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
  ctx.fillStyle = high ? theme.pinHigh : (theme.body === '#ffffff' ? '#e2e8f0' : '#334155')
  ctx.fill()
  ctx.strokeStyle = high ? theme.pinHigh : theme.pinLow
  ctx.lineWidth = 1.3 / zoom; ctx.stroke()
}

function wireView(from: CircuitNode, to: CircuitNode, w: Wire) {
  // Support both directions / pin sides for flexibility
  let a: Vec2 | null = null
  let b: Vec2 | null = null
  if (w.from.side === 'out') {
    const fi = from.outputs.findIndex((p) => p.id === w.from.pinId)
    if (fi >= 0) a = rightPinPos(from, fi)
  } else {
    const fi = from.inputs.findIndex((p) => p.id === w.from.pinId)
    if (fi >= 0) a = leftPinPos(from, fi)
  }
  if (w.to.side === 'in') {
    const ti = to.inputs.findIndex((p) => p.id === w.to.pinId)
    if (ti >= 0) b = leftPinPos(to, ti)
  } else {
    const ti = to.outputs.findIndex((p) => p.id === w.to.pinId)
    if (ti >= 0) b = rightPinPos(to, ti)
  }
  if (!a || !b) return null
  const pts = wireAnchors(a, b, w.mids)
  return { pts, mode: (w.straight ? 'straight' : 'smooth') as 'straight' | 'smooth' }
}

/**
 * Stroke a path through anchors.
 * - smooth + 2 pts: classic horizontal cubic (leaves right, enters left)
 * - smooth + 3+ pts: Catmull-Rom → cubic Bézier through every control point
 * - straight: pure polyline, point-to-point, no curves
 */
function strokeWirePath(ctx: CanvasRenderingContext2D, pts: Vec2[], mode: 'smooth' | 'straight') {
  if (pts.length < 2) return
  ctx.beginPath()
  ctx.moveTo(pts[0].x, pts[0].y)
  if (mode === 'straight') {
    for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y)
    return
  }
  // Default 2-point wire: horizontal cubic
  if (pts.length === 2) {
    const mx = pts[0].x + (pts[1].x - pts[0].x) / 2
    ctx.bezierCurveTo(mx, pts[0].y, mx, pts[1].y, pts[1].x, pts[1].y)
    return
  }
  // Catmull-Rom spline through all anchors → cubic Bézier segments
  for (let i = 0; i < pts.length - 1; i++) {
    const p0 = pts[i - 1] ?? pts[i]
    const p1 = pts[i]
    const p2 = pts[i + 1]
    const p3 = pts[i + 2] ?? p2
    const cp1x = p1.x + (p2.x - p0.x) / 6
    const cp1y = p1.y + (p2.y - p0.y) / 6
    const cp2x = p2.x - (p3.x - p1.x) / 6
    const cp2y = p2.y - (p3.y - p1.y) / 6
    ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, p2.x, p2.y)
  }
}

function drawScene(
  ctx: CanvasRenderingContext2D, sw: number, sh: number, dpr: number,
  cam: Camera, nodes: CircuitNode[], wires: Wire[], signal: SignalMap,
  selected: Set<string>, selectedWireId: string | null, hoverWireId: string | null,
  chipMeta: Record<string, { color: string }>,
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

  for (const w of wires) {
    const from = byId.get(w.from.nodeId), to = byId.get(w.to.nodeId)
    if (!from || !to) continue
    const vw = wireView(from, to, w)
    if (!vw) continue
    const high = wireActive(w), hover = hoverWireId === w.id, isSel = selectedWireId === w.id
    const pts = vw.pts
    const mode = vw.mode
    if (high) {
      ctx.save(); ctx.strokeStyle = theme.wireHigh + '30'; ctx.lineWidth = 7 / zoom
      strokeWirePath(ctx, pts, mode)
      ctx.stroke(); ctx.restore()
    }
    ctx.strokeStyle = isSel ? theme.sel : hover ? theme.wireHover : high ? theme.wireHigh : theme.wireLow
    ctx.lineWidth = isSel ? clamp(3 / zoom, 1.6, 3.4) : clamp(2.1 / zoom, 1.2, 2.6)
    if (hover || isSel) ctx.setLineDash([5 / zoom, 3 / zoom])
    strokeWirePath(ctx, pts, mode)
    ctx.stroke(); ctx.setLineDash([])

    // control point dots
    if (w.mids) {
      for (const m of w.mids) {
        ctx.beginPath(); ctx.arc(m.x, m.y, 4.5 / zoom, 0, Math.PI * 2)
        ctx.fillStyle = theme.body
        ctx.fill()
        ctx.lineWidth = 1.4 / zoom
        ctx.strokeStyle = isSel ? theme.sel : theme.wireHover
        ctx.stroke()
      }
    }
  }

  for (const n of nodes) drawNode(ctx, n, selected.has(n.id), signal, chipMeta, zoom, theme, dark)
  for (const n of nodes)
    for (const pin of enumeratePins(n))
      drawPin(ctx, pin.pos.x, pin.pos.y, !!signal[pinKey(pin.nodeId, pin.pinId)], zoom, theme)

  if (pending) {
    ctx.strokeStyle = theme.wireHigh; ctx.setLineDash([5 / zoom, 4 / zoom]); ctx.lineWidth = 1.9 / zoom
    strokeWirePath(ctx, [pending.startPos, pending.end], 'smooth')
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
  | { kind: 'wireMid'; wireId: string; midIndex: number }
  | null

export default function LogicMaker() {
  const saved = useMemo(() => loadState(), [])
  const [nodes, setNodes] = useState<CircuitNode[]>(saved.nodes ?? [])
  const [wires, setWires] = useState<Wire[]>(saved.wires ?? [])
  const [chips, setChips] = useState<ChipDefinition[]>(() => [...makeBuiltInChips(), ...(saved.chips ?? [])])
  const [selected, setSelected] = useState<Set<string>>(new Set())
  const [selectedWireId, setSelectedWireId] = useState<string | null>(null)
  const [placement, setPlacement] = useState<Placement>(null)
  const [camera, setCamera] = useState<Camera>(saved.camera ?? { zoom: 1, offsetX: 40, offsetY: 40 })
  const [editing, setEditing] = useState<EditSession | null>(null)
  const [createModal, setCreateModal] = useState(false)
  const [clockModal, setClockModal] = useState<{ id: string; period: number } | null>(null)
  const [renamePinModal, setRenamePinModal] = useState<{ nodeId: string; pinId: string; side: PinSide; name: string } | null>(null)
  const [colorModal, setColorModal] = useState<{ chipId: string; hex: string } | null>(null)
  const [chipName, setChipName] = useState('My Chip')
  const [chipColor, setChipColor] = useState(CHIP_COLORS[0])
  const [customHex, setCustomHex] = useState('#2563eb')
  const [history, setHistory] = useState<HistoryEntry[]>([])
  const [redoStack, setRedoStack] = useState<HistoryEntry[]>([])
  const [clipboard, setClipboard] = useState<{ nodes: CircuitNode[]; wires: Wire[] } | null>(null)
  const [wireMode, setWireMode] = useState<'drag' | 'click'>('drag') // drag or click-to-connect
  const [selectedMids, setSelectedMids] = useState<Set<string>>(new Set()) // "wireId:index"
  const [ctxMenu, setCtxMenu] = useState<ContextMenuState | null>(null)
  const [dark, setDark] = useState(saved.dark ?? false)
  const [, setFrameTick] = useState(0)

  const theme = dark ? DARK : LIGHT
  const canvasRef = useRef<HTMLCanvasElement>(null)
  const drag = useRef<DragMode>(null)
  const pan = useRef<{ startScreenX: number; startScreenY: number; startOffsetX: number; startOffsetY: number } | null>(null)
  const spaceDown = useRef(false)
  const pending = useRef<{ start: PinRef; startPos: Vec2 } | null>(null)
  const hoverWire = useRef<string | null>(null)
  const signal = useRef<SignalMap>({})
  const mousePos = useRef<Vec2>({ x: 0, y: 0 })
  const hasLoaded = useRef(false)
  const modalOpen = useRef(false)
  const buttonHeld = useRef<string | null>(null)

  const live = useRef({ nodes, wires, chips, selected, selectedWireId, placement, camera })
  useEffect(() => { live.current = { nodes, wires, chips, selected, selectedWireId, placement, camera } })
  useEffect(() => { modalOpen.current = !!(createModal || clockModal || renamePinModal || colorModal) }, [createModal, clockModal, renamePinModal, colorModal])

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
        nodes: live.current.nodes.map((n) => ({ ...n, position: { ...n.position } })),
        wires: live.current.wires.map((w) => ({ ...w, mids: w.mids?.map((m) => ({ ...m })) })),
      }
      const next = [...h, entry]
      return next.length > 80 ? next.slice(-80) : next
    })
    setRedoStack([]) // clear redo on new action
  }, [])

  const undo = useCallback(() => {
    setHistory((h) => {
      if (!h.length) return h
      const prev = h[h.length - 1]
      // push current to redo
      setRedoStack((r) => {
        const cur = {
          nodes: live.current.nodes.map((n) => ({ ...n, position: { ...n.position } })),
          wires: live.current.wires.map((w) => ({ ...w, mids: w.mids?.map((m) => ({ ...m })) })),
        }
        return [...r, cur].slice(-80)
      })
      setNodes(prev.nodes); setWires(prev.wires); setSelected(new Set()); setSelectedWireId(null); setSelectedMids(new Set())
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
      setNodes(next.nodes); setWires(next.wires); setSelected(new Set()); setSelectedWireId(null); setSelectedMids(new Set())
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
  /** find a draggable mid (control point) near p, on any wire */
  const findMidAt = (p: Vec2): { wireId: string; midIndex: number } | null => {
    const grab = 9 / live.current.camera.zoom
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
      // Sample path so hit-test matches what is drawn
      const samples: Vec2[] = []
      if (vw.mode === 'smooth' && pts.length === 2) {
        const mx = pts[0].x + (pts[1].x - pts[0].x) / 2
        for (let t = 0; t <= 1; t += 0.08) {
          const u = 1 - t
          samples.push({
            x: u * u * u * pts[0].x + 3 * u * u * t * mx + 3 * u * t * t * mx + t * t * t * pts[1].x,
            y: u * u * u * pts[0].y + 3 * u * u * t * pts[0].y + 3 * u * t * t * pts[1].y + t * t * t * pts[1].y,
          })
        }
      } else if (vw.mode === 'smooth' && pts.length > 2) {
        // sample Catmull-Rom segments coarsely
        for (let i = 0; i < pts.length - 1; i++) {
          const p0 = pts[i - 1] ?? pts[i]
          const p1 = pts[i]
          const p2 = pts[i + 1]
          const p3 = pts[i + 2] ?? p2
          for (let t = 0; t <= 1; t += 0.12) {
            const u = 1 - t
            const cp1x = p1.x + (p2.x - p0.x) / 6, cp1y = p1.y + (p2.y - p0.y) / 6
            const cp2x = p2.x - (p3.x - p1.x) / 6, cp2y = p2.y - (p3.y - p1.y) / 6
            samples.push({
              x: u * u * u * p1.x + 3 * u * u * t * cp1x + 3 * u * t * t * cp2x + t * t * t * p2.x,
              y: u * u * u * p1.y + 3 * u * u * t * cp1y + 3 * u * t * t * cp2y + t * t * t * p2.y,
            })
          }
        }
      } else {
        for (const pt of pts) samples.push(pt)
      }
      for (let i = 0; i < samples.length - 1; i++) {
        const d = distToSegment(p, samples[i], samples[i + 1])
        if (d < bestD) { bestD = d; best = w.id }
      }
    }
    return best
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
    setPlacement(null)
  }

  const onPointerDown = (e: React.PointerEvent) => {
    setCtxMenu(null)
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

    // 1) Nodes / buttons FIRST — higher priority than wires that may overlap them
    const node = findNodeAt(p)
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
          return
        }
      }
      if (node.kind === 'CLOCK') {
        // Only open modal if click is inside the body, not on a pin
        const pinHit = findPinAt(p)
        if (!pinHit) {
          setClockModal({ id: node.id, period: node.period ?? 30 })
          setSelected(new Set([node.id]))
          setSelectedWireId(null)
          return
        }
      }
      // fall through to pin / move handling below
    }

    // 2) Pins — higher priority than body-drag so wiring still works
    // Allow starting a wire from ANY pin (in or out). Direction is normalized later.
    const pin = findPinAt(p)
    if (pin) {
      if (pending.current) {
        // finish connection (click-to-connect or second click)
        const start = pending.current.start
        const end: PinRef = { nodeId: pin.nodeId, pinId: pin.pinId, side: pin.side }
        // normalize: always store from=out → to=in when possible
        let from = start, to = end
        if (start.side === 'in' && end.side === 'out') {
          from = end; to = start
        } else if (start.side === end.side) {
          // same side — still allow but keep order as drawn
        }
        if (!isPinRefEqual(from, to) && from.nodeId !== to.nodeId) {
          pushHistory()
          finishWire(from, to)
        }
        pending.current = null
        drag.current = null
        return
      }
      // start new wire
      if (wireMode === 'click') {
        pending.current = { start: { nodeId: pin.nodeId, pinId: pin.pinId, side: pin.side }, startPos: pin.pos }
      } else {
        drag.current = { kind: 'wire', start: { nodeId: pin.nodeId, pinId: pin.pinId, side: pin.side }, startPos: pin.pos, end: pin.pos }
      }
      return
    }

    // cancel pending wire on empty click
    if (pending.current && !pin) {
      pending.current = null
      return
    }

    // 2b) Body drag (after pin check)
    if (node) {
      const multi = e.shiftKey || selected.has(node.id)
      const next = new Set<string>(multi ? selected : [])
      next.add(node.id)
      setSelected(next)
      setSelectedWireId(null)
      const origin = new Map<string, Vec2>()
      for (const n of live.current.nodes) if (next.has(n.id)) origin.set(n.id, { ...n.position })
      drag.current = { kind: 'move', ids: Array.from(next), startWorld: p, origin }
      return
    }

    // 3) Control-point drag
    const mid = findMidAt(p)
    if (mid) {
      drag.current = { kind: 'wireMid', wireId: mid.wireId, midIndex: mid.midIndex }
      setSelectedWireId(mid.wireId)
      setSelected(new Set())
      return
    }

    // 4) Wire — double-click adds a point ON the segment; single-click selects
    const hw = findHoveredWire(p)
    if (hw && e.detail === 2) {
      pushHistory()
      const byId = new Map(live.current.nodes.map((n) => [n.id, n]))
      setWires((ws) => ws.map((w) => {
        if (w.id !== hw) return w
        const from = byId.get(w.from.nodeId), to = byId.get(w.to.nodeId)
        if (!from || !to) return w
        const vw = wireView(from, to, w)
        if (!vw) return w
        const mids = insertMidAtClick(vw.pts, w.mids, p)
        return { ...w, mids, straight: w.straight }
      }))
      setSelectedWireId(hw)
      setSelected(new Set())
      return
    }
    if (hw) {
      setSelectedWireId(hw)
      setSelected(new Set())
      return
    }

    setSelected(new Set())
    setSelectedWireId(null)
    drag.current = { kind: 'box', startX: p.x, startY: p.y, endX: p.x, endY: p.y }
  }

  const onPointerMove = (e: React.PointerEvent) => {
    const r = canvasRect()
    const sx = e.clientX - r.left, sy = e.clientY - r.top
    if (pan.current) {
      setCamera((c) => ({
        ...c,
        offsetX: pan.current!.startOffsetX + (sx - pan.current!.startScreenX),
        offsetY: pan.current!.startOffsetY + (sy - pan.current!.startScreenY),
      }))
      return
    }
    const p = screenToWorld(sx, sy)
    mousePos.current = p
    if (drag.current?.kind === 'box') { drag.current.endX = p.x; drag.current.endY = p.y }
    else if (drag.current?.kind === 'wire') drag.current.end = p
    else if (drag.current?.kind === 'wireMid') {
      const d = drag.current
      // Free placement — no magnetic grid on control points
      const np = { x: p.x, y: p.y }
      setWires((ws) => ws.map((w) => {
        if (w.id !== d.wireId || !w.mids) return w
        const mids = w.mids.slice()
        mids[d.midIndex] = np
        return { ...w, mids }
      }))
    } else if (drag.current?.kind === 'move') {
      const d = drag.current, dx = p.x - d.startWorld.x, dy = p.y - d.startWorld.y
      const idSet = new Set(d.ids)
      setNodes((ns) => ns.map((n) => idSet.has(n.id)
        ? { ...n, position: { x: d.origin.get(n.id)!.x + dx, y: d.origin.get(n.id)!.y + dy } } : n))
    } else hoverWire.current = findHoveredWire(p)
  }

  const onPointerUp = (e: React.PointerEvent) => {
    // release momentary button
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
    if (d?.kind === 'box') {
      const minX = Math.min(d.startX, d.endX), maxX = Math.max(d.startX, d.endX)
      const minY = Math.min(d.startY, d.endY), maxY = Math.max(d.startY, d.endY)
      const next = new Set<string>()
      for (const n of live.current.nodes) {
        const b = nodeBox(n)
        if (b.x < maxX && b.x + b.w > minX && b.y < maxY && b.y + b.h > minY) next.add(n.id)
      }
      setSelected(next)
    } else if (d?.kind === 'wire') {
      const pin = findPinAt(p)
      if (pin) {
        const end: PinRef = { nodeId: pin.nodeId, pinId: pin.pinId, side: pin.side }
        let from = d.start, to = end
        if (d.start.side === 'in' && end.side === 'out') {
          from = end; to = d.start
        }
        if (!isPinRefEqual(from, to) && from.nodeId !== to.nodeId) {
          pushHistory()
          finishWire(from, to)
        }
        pending.current = null
      } else if (!findNodeAt(p)) {
        // release on empty → keep as pending for click-to-connect style
        pending.current = { start: d.start, startPos: d.startPos }
      } else {
        pending.current = { start: d.start, startPos: d.startPos }
      }
    } else if (d?.kind === 'wireMid') {
      pushHistory()
    } else if (d?.kind === 'move') {
      const idSet = new Set(d.ids)
      setNodes((ns) => ns.map((n) => idSet.has(n.id)
        ? { ...n, position: { x: snap(n.position.x), y: snap(n.position.y) } } : n))
    }
    drag.current = null
  }

  const finishWire = (from: PinRef, to: PinRef) => {
    if (isPinRefEqual(from, to) || from.nodeId === to.nodeId) return
    // Prefer out→in direction for consistent rendering & signal flow
    let f = from, t = to
    if (from.side === 'in' && to.side === 'out') {
      f = to; t = from
    }
    // Remove any existing wire to the same input pin (one driver rule)
    setWires((ws) => [...ws.filter((w) => !(t.side === 'in' && isPinRefEqual(w.to, t))), createWire(f, t)])
  }

  const deleteSelection = () => {
    if (selectedMids.size > 0) {
      pushHistory()
      setWires((ws) => ws.map((w) => {
        if (!w.mids) return w
        const keep = w.mids.filter((_, i) => !selectedMids.has(`${w.id}:${i}`))
        return { ...w, mids: keep.length ? keep : undefined }
      }))
      setSelectedMids(new Set())
      return
    }
    if (selectedWireId) {
      pushHistory()
      setWires((ws) => ws.filter((w) => w.id !== selectedWireId))
      setSelectedWireId(null)
      return
    }
    if (!selected.size) return
    pushHistory()
    const ids = new Set(selected)
    setNodes((ns) => ns.filter((n) => !ids.has(n.id)))
    setWires((ws) => ws.filter((w) => !ids.has(w.from.nodeId) && !ids.has(w.to.nodeId)))
    setSelected(new Set())
  }

  const copySelection = () => {
    if (!selected.size) return
    const ids = new Set(selected)
    setClipboard({
      nodes: nodes.filter((n) => ids.has(n.id)).map((n) => ({ ...n, position: { ...n.position } })),
      wires: wires.filter((w) => ids.has(w.from.nodeId) && ids.has(w.to.nodeId)),
    })
  }
  const cutSelection = () => { copySelection(); deleteSelection() }
  const pasteClipboard = () => {
    if (!clipboard?.nodes.length) return
    pushHistory()
    const idMap = new Map<string, string>()
    const offset = 48
    const newNodes = clipboard.nodes.map((n) => {
      const newId = uid(n.kind.toLowerCase())
      idMap.set(n.id, newId)
      return { ...n, id: newId, position: { x: n.position.x + offset, y: n.position.y + offset } }
    })
    const newWires = clipboard.wires.map((w) => ({
      id: uid('w'),
      from: { ...w.from, nodeId: idMap.get(w.from.nodeId)! },
      to: { ...w.to, nodeId: idMap.get(w.to.nodeId)! },
      mids: w.mids?.map((m) => ({ x: m.x + offset, y: m.y + offset })),
    }))
    setNodes((ns) => [...ns, ...newNodes])
    setWires((ws) => [...ws, ...newWires])
    setSelected(new Set(newNodes.map((n) => n.id)))
    setSelectedWireId(null)
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
    setSelected(new Set()); setSelectedWireId(null); setPlacement(null); pending.current = null
    // Center the chip content in the viewport
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
    setCamera({
      zoom,
      offsetX: cw / 2 - cx * zoom,
      offsetY: ch / 2 - cy * zoom,
    })
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
      setSelected(session.snapSelected); setSelectedWireId(null); setCamera(session.snapCamera)
      setPlacement(null); pending.current = null
      return null
    })
  }

  const deleteCustomChip = (chipId: string) => {
    const chip = chipsById[chipId]
    if (!chip || chip.builtin) return
    if (!window.confirm(`Delete “${chip.name}”?`)) return
    pushHistory()
    const remove = new Set(live.current.nodes.filter((n) => n.chipId === chipId).map((n) => n.id))
    setChips((cs) => cs.filter((c) => c.id !== chipId))
    setNodes((ns) => ns.filter((n) => !remove.has(n.id)))
    setWires((ws) => ws.filter((w) => !remove.has(w.from.nodeId) && !remove.has(w.to.nodeId)))
    setSelected((s) => { const n = new Set(s); remove.forEach((id) => n.delete(id)); return n })
    if (placement?.type === 'CHIP' && placement.chipId === chipId) setPlacement(null)
  }

  const renameChipInEdit = (name: string) => {
    if (!editing) return
    setChips((cs) => cs.map((c) => c.id === editing.chipId ? { ...c, name } : c))
  }

  const openColorModal = (chipId: string) => {
    const chip = chipsById[chipId]
    if (!chip) return
    setColorModal({ chipId, hex: chip.color })
  }
  const applyChipColor = () => {
    if (!colorModal) return
    setChips((cs) => cs.map((c) => c.id === colorModal.chipId ? { ...c, color: colorModal.hex } : c))
    setColorModal(null)
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
    // also update label of INPUT/OUTPUT node itself if it's a top-level I/O
    setNodes((ns) => ns.map((n) => {
      if (n.id !== nodeId) return n
      if ((n.kind === 'INPUT' || n.kind === 'OUTPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK') && side === (n.kind === 'OUTPUT' ? 'in' : 'out')) {
        return { ...n, label: name.trim() || n.label }
      }
      return n
    }))
    setRenamePinModal(null)
  }

  const onDoubleClick = (e: React.MouseEvent) => {
    if (placement) return
    const p = screenToWorld(e.clientX - canvasRect().left, e.clientY - canvasRect().top)
    if (findMidAt(p)) return // handled by pointerdown mid-drag, not a rename target
    if (findHoveredWire(p)) return // handled in onPointerDown (adds a control point)
    const pin = findPinAt(p)
    if (pin) {
      // Rename only allowed for INPUT / OUTPUT / BUTTON / CLOCK (their visible labels become pin names when packaged)
      const n = pin.node
      if (n.kind === 'INPUT' || n.kind === 'OUTPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK') {
        const side = n.kind === 'OUTPUT' ? 'in' : 'out'
        const pinList = side === 'in' ? n.inputs : n.outputs
        const thePin = pinList.find((x) => x.id === pin.pinId) ?? pinList[0]
        setRenamePinModal({
          nodeId: n.id,
          pinId: thePin?.id ?? pin.pinId,
          side,
          name: n.label, // use node label for I/O (what user sees)
        })
      }
      return
    }
    if (editing) return
    const node = findNodeAt(p)
    if (node?.kind === 'CHIP' && node.chipId && !chipsById[node.chipId]?.builtin)
      enterEditChip(node.chipId)
  }

  const onContextMenu = (e: React.MouseEvent) => {
    e.preventDefault()
    const p = posFromEvent(e)
    const node = findNodeAt(p)
    const wireId = findHoveredWire(p)
    let target: ContextMenuState['target'] = 'canvas'
    let nodeId: string | undefined, wId: string | undefined
    if (node) {
      target = node.kind === 'CHIP' && node.chipId && !chipsById[node.chipId]?.builtin ? 'chip' : 'node'
      nodeId = node.id
      if (!selected.has(node.id)) setSelected(new Set([node.id]))
      setSelectedWireId(null)
    } else if (wireId) {
      target = 'wire'; wId = wireId
      setSelectedWireId(wireId); setSelected(new Set())
    }
    setCtxMenu({ x: e.clientX, y: e.clientY, world: p, target, nodeId, wireId: wId })
  }

  const ctxAction = (action: string) => {
    if (!ctxMenu) return
    const wireId = ctxMenu.wireId
    setCtxMenu(null)
    if (action === 'cut') cutSelection()
    else if (action === 'copy') copySelection()
    else if (action === 'paste') pasteClipboard()
    else if (action === 'delete') {
      if (wireId) { pushHistory(); setWires((ws) => ws.filter((w) => w.id !== wireId)); setSelectedWireId(null) }
      else deleteSelection()
    } else if (action === 'edit' && ctxMenu.nodeId) {
      const n = nodes.find((x) => x.id === ctxMenu.nodeId)
      if (n?.chipId) enterEditChip(n.chipId)
    } else if (action === 'color' && ctxMenu.nodeId) {
      const n = nodes.find((x) => x.id === ctxMenu.nodeId)
      if (n?.chipId) openColorModal(n.chipId)
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
    } else if (action === 'straight' && wireId) {
      pushHistory()
      setWires((ws) => ws.map((w) => w.id === wireId ? { ...w, straight: true } : w))
    } else if (action === 'smooth' && wireId) {
      pushHistory()
      setWires((ws) => ws.map((w) => w.id === wireId ? { ...w, straight: false } : w))
    } else if (action === 'clearMids' && wireId) {
      pushHistory()
      setWires((ws) => ws.map((w) => w.id === wireId ? { ...w, mids: undefined } : w))
    } else if (action === 'rename' && ctxMenu.nodeId) {
      const n = nodes.find((x) => x.id === ctxMenu.nodeId)
      if (!n) return
      // Rename the visible label of I/O nodes (becomes pin name when packaged into a chip)
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
    setNodes([]); setWires([]); setSelected(new Set()); setSelectedWireId(null); setPlacement(null)
    pending.current = null; simulator.reset(); signal.current = {}
  }

  const exportJSON = () => {
    const data = { version: 1, nodes, wires, chips: chips.filter((c) => !c.builtin), camera, dark }
    const blob = new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a'); a.href = url; a.download = `logicmaker-${Date.now()}.json`; a.click()
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
        setSelected(new Set()); setSelectedWireId(null); setPlacement(null); pending.current = null
      } catch { window.alert('Invalid file') }
    }
    input.click()
  }

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
      if (mod && (e.key === 'z' || e.key === 'Z') && !e.shiftKey) { e.preventDefault(); undo(); return }
      if (mod && ((e.key === 'y' || e.key === 'Y') || ((e.key === 'z' || e.key === 'Z') && e.shiftKey))) { e.preventDefault(); redo(); return }
      if (mod && (e.key === 'c' || e.key === 'C')) { e.preventDefault(); copySelection(); return }
      if (mod && (e.key === 'v' || e.key === 'V')) { e.preventDefault(); pasteClipboard(); return }
      if (mod && (e.key === 'x' || e.key === 'X')) { e.preventDefault(); cutSelection(); return }
      if (e.key === 'Escape') {
        pending.current = null; setPlacement(null); setCreateModal(false)
        setClockModal(null); setRenamePinModal(null); setColorModal(null); setCtxMenu(null)
        setSelected(new Set()); setSelectedWireId(null); setSelectedMids(new Set())
      }
      if ((e.key === 'Delete' || e.key === 'Backspace') && (live.current.selected.size > 0 || live.current.selectedWireId || selectedMids.size > 0)) {
        e.preventDefault(); deleteSelection()
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
  }, [undo, redo])

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
        s.selected, s.selectedWireId, hoverWire.current, chipMeta, pnd, box, placingNode, theme, dark)
    }
    loop()
    return () => cancelAnimationFrame(raf)
  }, [theme, dark])

  const btn = 'inline-flex flex-col items-center gap-0.5 rounded-md px-2.5 py-1.5 text-[11px] font-medium transition select-none'
  const active = dark ? 'bg-sky-900/50 text-sky-300 ring-1 ring-sky-500/50' : 'bg-blue-100 text-blue-700 ring-1 ring-blue-400/60'
  const idle = dark ? 'text-slate-300 hover:bg-slate-700' : 'text-slate-600 hover:bg-slate-100 hover:text-slate-900'
  const isPrim = (k: PrimitiveType) => placement?.type === 'PRIMITIVE' && placement.kind === k
  const isChip = (id: string) => placement?.type === 'CHIP' && placement.chipId === id
  const builtinChips = chips.filter((c) => c.builtin)
  const customChips = chips.filter((c) => !c.builtin)
  const editingChip = editing ? chipsById[editing.chipId] : null

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
            <button
              onClick={() => openColorModal(editingChip.id)}
              className={`grid h-6 w-6 shrink-0 place-items-center rounded-full ring-1 ${dark ? 'ring-slate-600' : 'ring-slate-300'}`}
              style={{ background: editingChip.color }}
              title="Change color"
            />
            <span className="text-[11px] opacity-50">Edit mode — double-click pins to rename</span>
            <div className="flex-1" />
            <button
              onClick={() => {
                if (!editingChip) return
                const id = editingChip.id
                exitEditChip(false)
                deleteCustomChip(id)
              }}
              className={`${btn} text-red-500 hover:bg-red-50`}
              title="Delete this chip"
            >
              <Trash2 size={14} /> Delete Chip
            </button>
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
            <button onClick={exportJSON} className={`${btn} ${idle}`} title="Export JSON"><Download size={14} /></button>
            <button onClick={importJSON} className={`${btn} ${idle}`} title="Import JSON"><Upload size={14} /></button>
            <button onClick={centerView} className={`${btn} ${idle}`} title="Center view on scheme"><Crosshair size={14} /></button>
            <button onClick={() => setCamera({ zoom: 1, offsetX: 40, offsetY: 40 })} className={`${btn} ${idle}`} title="Reset zoom"><RotateCcw size={14} /></button>
            <span className="font-mono text-[11px] opacity-50">{Math.round(camera.zoom * 100)}%</span>
            <div className={`mx-1 h-5 w-px ${dark ? 'bg-slate-600' : 'bg-slate-200'}`} />
            <button
              onClick={() => setWireMode((m) => m === 'drag' ? 'click' : 'drag')}
              className={`${btn} ${wireMode === 'click' ? active : idle}`}
              title={wireMode === 'drag' ? 'Wire mode: Drag (switch to Click-to-Connect)' : 'Wire mode: Click-to-Connect (switch to Drag)'}
            >
              {wireMode === 'drag' ? <MousePointer2 size={14} /> : <Link2 size={14} />}
              <span className="text-[10px]">{wireMode === 'drag' ? 'Drag' : 'Click'}</span>
            </button>
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
          <div className="flex gap-1.5">
            {(['INPUT', 'OUTPUT', 'CLOCK', 'BUTTON'] as PrimitiveType[]).map((k) => (
              <button key={k} onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
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
          <div className="flex gap-1.5">
            {(['AND', 'OR', 'NOT'] as PrimitiveType[]).map((k) => (
              <button key={k} onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
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
          <div className="flex gap-1.5">
            {builtinChips.map((c) => (
              <button key={c.id} onClick={() => setPlacement({ type: 'CHIP', chipId: c.id })}
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
            <section className="flex min-w-0 flex-col">
              <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider opacity-50">Custom</h3>
              <div className="flex gap-2.5 overflow-x-auto pt-1">
                {customChips.map((c) => (
                  <div key={c.id} className="relative flex flex-col items-center">
                    <button
                      type="button"
                      onClick={(e) => { e.stopPropagation(); enterEditChip(c.id) }}
                      className={`absolute -right-1 -top-1 z-10 grid h-5 w-5 place-items-center rounded-full shadow ring-1 ${dark ? 'bg-slate-700 text-slate-200 ring-slate-600 hover:bg-slate-600' : 'bg-white text-slate-600 ring-slate-200 hover:bg-slate-50'}`}
                      title="Edit"
                    >
                      <Pencil size={11} />
                    </button>
                    <button onClick={() => setPlacement({ type: 'CHIP', chipId: c.id })}
                      className={`${btn} ${isChip(c.id) ? active : idle}`}>
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

      {ctxMenu && (
        <div className={`fixed z-50 overflow-hidden rounded-lg border py-1 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}
          style={{ left: ctxMenu.x, top: ctxMenu.y }} onMouseLeave={() => setCtxMenu(null)}>
          {ctxMenu.target === 'wire' ? (
            <>
              <button className={`flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`}
                onClick={() => ctxAction('addPoint')}>
                <Pencil size={14} /> Add point
              </button>
              <button className={`flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`}
                onClick={() => ctxAction('smooth')}>
                Smooth curve
              </button>
              <button className={`flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`}
                onClick={() => ctxAction('straight')}>
                Straight segments
              </button>
              <button className={`flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`}
                onClick={() => ctxAction('clearMids')}>
                Clear control points
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
                <button key={item.a} className={`flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`}
                  onClick={() => ctxAction(item.a)}>
                  {item.icon} {item.label}
                  <span className="ml-auto text-[10px] opacity-50">{item.k}</span>
                </button>
              ))}
              <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
              <button className="flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm text-red-500 hover:bg-red-50"
                onClick={() => ctxAction('delete')}>
                <Trash2 size={14} /> Delete
              </button>
              {ctxMenu.target === 'node' && ctxMenu.nodeId && (() => {
                const n = nodes.find((x) => x.id === ctxMenu.nodeId)
                return n && (n.kind === 'INPUT' || n.kind === 'OUTPUT' || n.kind === 'BUTTON' || n.kind === 'CLOCK')
              })() && (
                  <>
                    <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                    <button className={`flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`}
                      onClick={() => ctxAction('rename')}><Type size={14} /> Rename</button>
                  </>
                )}
              {ctxMenu.target === 'chip' && (
                <>
                  <div className={`my-1 border-t ${dark ? 'border-slate-600' : 'border-slate-100'}`} />
                  <button className={`flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`}
                    onClick={() => ctxAction('edit')}><Pencil size={14} /> Edit</button>
                  <button className={`flex w-full items-center gap-2 px-3 py-1.5 text-left text-sm ${dark ? 'text-slate-200 hover:bg-slate-700' : 'text-slate-700 hover:bg-slate-50'}`}
                    onClick={() => ctxAction('color')}><Palette size={14} /> Change color</button>
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

      {colorModal && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/40">
          <div className={`w-80 rounded-xl border p-5 shadow-xl ${dark ? 'border-slate-600 bg-slate-800' : 'border-slate-200 bg-white'}`}>
            <h2 className="mb-3 text-sm font-semibold">Chip Color</h2>
            <div className="mb-2 flex flex-wrap gap-2">
              {CHIP_COLORS.map((c) => (
                <button key={c} onClick={() => setColorModal({ ...colorModal, hex: c })}
                  className={`h-7 w-7 rounded-full ring-2 ${colorModal.hex === c ? 'ring-slate-800 ring-offset-1' : 'ring-transparent'}`}
                  style={{ background: c }} />
              ))}
            </div>
            <div className="mb-5 flex items-center gap-2">
              <input type="color" value={colorModal.hex} onChange={(e) => setColorModal({ ...colorModal, hex: e.target.value })}
                className="h-8 w-10 cursor-pointer rounded border-0" />
              <span className="text-[11px] opacity-60">Custom color</span>
            </div>
            <div className="flex justify-end gap-2">
              <button onClick={() => setColorModal(null)} className={`${btn} ${idle}`}>Cancel</button>
              <button onClick={applyChipColor} className={`${btn} bg-blue-50 text-blue-700`}>Apply</button>
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
    </div>
  )
}