import React, {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
} from 'react'

/* =====================================================================
 *  LogicCraft — Light Blueprint Theme (complete rewrite)
 *  Single-file, self-contained React component.
 * ===================================================================== */

type PinSide = 'in' | 'out'
interface Vec2 { x: number; y: number }
interface PinRef { nodeId: string; pinId: string; side: PinSide }
type PrimitiveType = 'AND' | 'OR' | 'NOT' | 'INPUT' | 'OUTPUT'
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
}
interface Wire {
  id: string
  from: PinRef
  to: PinRef
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
type Tool = 'select' | 'wire'
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

interface HistoryEntry {
  nodes: CircuitNode[]
  wires: Wire[]
}

const pinKey = (n: string, p: string) => `${n}:${p}`
const isPinRefEqual = (a: PinRef, b: PinRef) =>
  a.nodeId === b.nodeId && a.pinId === b.pinId && a.side === b.side

/* ------------------------------------------------------------------ */
/* Geometry                                                            */
/* ------------------------------------------------------------------ */
const GRID = 24
const NODE_W = 100
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

const nodeRows = (n: CircuitNode) => Math.max(n.inputs.length, n.outputs.length, 1)
const nodeHeight = (n: CircuitNode) =>
  NODE_PAD * 2 + PIN_SPACING * Math.max(nodeRows(n) - 1, 0) + PIN_SPACING

const nodeBox = (n: CircuitNode) => ({
  x: n.position.x,
  y: n.position.y,
  w: NODE_W,
  h: nodeHeight(n),
})

const leftPinPos = (n: CircuitNode, i: number): Vec2 => ({
  x: n.position.x,
  y: n.position.y + NODE_PAD + PIN_SPACING / 2 + i * PIN_SPACING,
})
const rightPinPos = (n: CircuitNode, i: number): Vec2 => ({
  x: n.position.x + NODE_W,
  y: n.position.y + NODE_PAD + PIN_SPACING / 2 + i * PIN_SPACING,
})

interface EnumeratedPin {
  nodeId: string
  pinId: string
  side: PinSide
  index: number
  pos: Vec2
  node: CircuitNode
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
  const dx = b.x - a.x
  const dy = b.y - a.y
  const l2 = dx * dx + dy * dy
  if (l2 === 0) return Math.hypot(p.x - a.x, p.y - a.y)
  let t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / l2
  t = Math.max(0, Math.min(1, t))
  return Math.hypot(p.x - (a.x + t * dx), p.y - (a.y + t * dy))
}

/* ------------------------------------------------------------------ */
/* Factory                                                             */
/* ------------------------------------------------------------------ */
const PRIMITIVE_SPEC: Record<PrimitiveType, { label: string; inputs: string[]; outputs: string[] }> = {
  AND: { label: 'AND', inputs: ['A', 'B'], outputs: ['OUT'] },
  OR: { label: 'OR', inputs: ['A', 'B'], outputs: ['OUT'] },
  NOT: { label: 'NOT', inputs: ['IN'], outputs: ['OUT'] },
  INPUT: { label: 'IN', inputs: [], outputs: ['OUT'] },
  OUTPUT: { label: 'OUT', inputs: ['IN'], outputs: [] },
}

const makePins = (names: string[]): Pin[] => names.map((name) => ({ id: name.toLowerCase(), name }))

function createPrimitiveNode(kind: PrimitiveType, position: Vec2, label?: string): CircuitNode {
  const spec = PRIMITIVE_SPEC[kind]
  return {
    id: uid(kind.toLowerCase()),
    kind,
    label: label ?? spec.label,
    position,
    inputs: makePins(spec.inputs),
    outputs: makePins(spec.outputs),
    ...(kind === 'INPUT' ? { value: false } : {}),
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

const createWire = (from: PinRef, to: PinRef): Wire => ({ id: uid('w'), from, to })

/* ------------------------------------------------------------------ */
/* Built-in flip-flops                                                 */
/* ------------------------------------------------------------------ */
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
  const Qbar = createPrimitiveNode('OUTPUT', U(5.5, 2), 'Q̄')
  return {
    id: 'builtin-rs-latch',
    name: 'RS Latch',
    color: '#0ea5e9',
    builtin: true,
    inputNodeIds: [R.id, S.id],
    outputNodeIds: [Q.id, Qbar.id],
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
  const Qbar = createPrimitiveNode('OUTPUT', U(7.5, 2), 'Q̄')
  return {
    id: 'builtin-d-latch',
    name: 'D Latch',
    color: '#8b5cf6',
    builtin: true,
    inputNodeIds: [D.id, EN.id],
    outputNodeIds: [Q.id, Qbar.id],
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

/* ------------------------------------------------------------------ */
/* Compiler – full recursive flattening with isolation                 */
/* ------------------------------------------------------------------ */
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

const MAX_DEPTH = 20

function compileCircuit(
  circuit: { nodes: CircuitNode[]; wires: Wire[] },
  chips: Record<string, ChipDefinition>,
): CompiledCircuit {
  const gates: CompiledGate[] = []
  const drivers = new Map<string, string>()
  const aliases = new Map<string, string>()
  const inputNets: Record<string, string> = {}

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
        case 'AND':
        case 'OR':
        case 'NOT':
          gates.push({
            key: id,
            type: node.kind,
            inputs: node.inputs.map(() => null),
            out: pinKey(id, node.outputs[0].id),
          })
          break
        case 'INPUT':
          if (prefix === '') inputNets[node.id] = pinKey(id, 'out')
          break
        case 'OUTPUT':
          break
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
      const v = resolveOut(alias, seen)
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
    if (drive === undefined) return null
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

  const gateNodeInputs = new Map<string, string[]>()
  for (const node of circuit.nodes) {
    if (node.kind === 'AND' || node.kind === 'OR' || node.kind === 'NOT') {
      gateNodeInputs.set(node.id, node.inputs.map((p) => pinKey(node.id, p.id)))
    }
  }
  for (const g of gates) {
    const keys = gateNodeInputs.get(g.key) ?? []
    g.inputs = keys.map((k) => resolveIn(k))
  }

  const pinNets: Record<string, string | null> = {}
  for (const node of circuit.nodes) {
    for (const p of node.inputs) pinNets[pinKey(node.id, p.id)] = resolveIn(pinKey(node.id, p.id))
    for (const p of node.outputs) pinNets[pinKey(node.id, p.id)] = resolveOut(pinKey(node.id, p.id), new Set())
  }
  return { gates, inputNets, pinNets }
}

/* ------------------------------------------------------------------ */
/* Simulator                                                           */
/* ------------------------------------------------------------------ */
const SETTLE_PASSES = 72
const SIM_TPS = 60

class Simulator {
  private state = new Map<string, boolean>()
  private compiled: CompiledCircuit = { gates: [], inputNets: {}, pinNets: {} }

  load(c: CompiledCircuit) {
    const next = new Map<string, boolean>()
    for (const g of c.gates) next.set(g.out, this.state.get(g.out) ?? false)
    for (const net of Object.values(c.inputNets)) next.set(net, this.state.get(net) ?? false)
    this.state = next
    this.compiled = c
  }

  reset() {
    for (const k of this.state.keys()) this.state.set(k, false)
  }

  private applyInputs(nodes: CircuitNode[]) {
    for (const n of nodes) {
      if (n.kind !== 'INPUT') continue
      const net = this.compiled.inputNets[n.id]
      if (net) this.state.set(net, !!n.value)
    }
  }

  private read(net: string | null) {
    return net === null ? false : (this.state.get(net) ?? false)
  }

  tick(nodes: CircuitNode[]) {
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
          this.state.set(gates[i].out, results[i])
          changed = true
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

/* ------------------------------------------------------------------ */
/* Packaging                                                           */
/* ------------------------------------------------------------------ */
const CHIP_ACCENTS = [
  '#2563eb', '#059669', '#d97706', '#dc2626', '#7c3aed',
  '#0891b2', '#be185d', '#4f46e5', '#0d9488', '#b45309',
]

function packageSelectionInto(
  name: string,
  color: string,
  nodes: CircuitNode[],
  wires: Wire[],
  selected: Set<string>,
  existingId?: string,
): ChipDefinition | null {
  const sel = nodes.filter((n) => selected.has(n.id))
  if (sel.length === 0) return null
  const ids = new Set(sel.map((n) => n.id))
  const inputs = sel.filter((n) => n.kind === 'INPUT').sort((a, b) => a.position.y - b.position.y)
  const outputs = sel.filter((n) => n.kind === 'OUTPUT').sort((a, b) => a.position.y - b.position.y)
  if (inputs.length === 0 || outputs.length === 0) return null
  const innerWires = wires.filter((w) => ids.has(w.from.nodeId) && ids.has(w.to.nodeId))
  return {
    id: existingId ?? uid('chip'),
    name,
    color,
    builtin: false,
    inputNodeIds: inputs.map((n) => n.id),
    outputNodeIds: outputs.map((n) => n.id),
    nodes: sel,
    wires: innerWires,
  }
}

function centroidOf(nodes: CircuitNode[]): Vec2 {
  if (!nodes.length) return { x: 0, y: 0 }
  const s = nodes.reduce((a, n) => ({ x: a.x + n.position.x, y: a.y + n.position.y }), { x: 0, y: 0 })
  return { x: Math.round(s.x / nodes.length), y: Math.round(s.y / nodes.length) }
}

/* ------------------------------------------------------------------ */
/* Renderer – Blueprint / Paper                                        */
/* ------------------------------------------------------------------ */
const CANVAS_BG = '#f1f5f9'
const GRID_DOT = '#cbd5e1'
const WIRE_HIGH = '#2563eb'
const WIRE_LOW = '#64748b'
const WIRE_HOVER = '#94a3b8'
const PIN_HIGH = '#2563eb'
const PIN_LOW = '#94a3b8'
const BODY_FILL = '#ffffff'
const BODY_EDGE = '#1e293b'
const LABEL = '#0f172a'
const SEL = '#2563eb'

const roundRect = (
  ctx: CanvasRenderingContext2D,
  x: number, y: number, w: number, h: number, r: number,
) => {
  ctx.beginPath()
  ctx.moveTo(x + r, y)
  ctx.arcTo(x + w, y, x + w, y + h, r)
  ctx.arcTo(x + w, y + h, x, y + h, r)
  ctx.arcTo(x, y + h, x, y, r)
  ctx.arcTo(x, y, x + w, y, r)
  ctx.closePath()
}

function drawGrid(
  ctx: CanvasRenderingContext2D,
  left: number, top: number, right: number, bottom: number, zoom: number,
) {
  ctx.fillStyle = GRID_DOT
  const r = clamp(1.1 / zoom, 0.6, 1.5)
  const x0 = Math.floor(left / GRID) * GRID
  const y0 = Math.floor(top / GRID) * GRID
  for (let x = x0; x < right; x += GRID) {
    for (let y = y0; y < bottom; y += GRID) {
      ctx.beginPath()
      ctx.arc(x, y, r, 0, Math.PI * 2)
      ctx.fill()
    }
  }
}

function cubic(a: Vec2, b: Vec2) {
  const mx = a.x + (b.x - a.x) / 2
  return { a, c1: { x: mx, y: a.y }, c2: { x: mx, y: b.y }, b }
}

function drawBody(
  ctx: CanvasRenderingContext2D,
  n: CircuitNode,
  accent: string | null,
  selected: boolean,
  zoom: number,
) {
  const b = nodeBox(n)
  if (selected) {
    ctx.save()
    ctx.strokeStyle = SEL
    ctx.lineWidth = 2.8 / zoom
    roundRect(ctx, b.x - 3.5, b.y - 3.5, b.w + 7, b.h + 7, 10)
    ctx.stroke()
    ctx.restore()
  }
  // white body
  ctx.fillStyle = BODY_FILL
  roundRect(ctx, b.x, b.y, b.w, b.h, 8)
  ctx.fill()
  // crisp black border
  ctx.strokeStyle = BODY_EDGE
  ctx.lineWidth = 1.6
  roundRect(ctx, b.x, b.y, b.w, b.h, 8)
  ctx.stroke()
  // colored header banner – strictly inside
  if (accent) {
    ctx.save()
    roundRect(ctx, b.x + 1.5, b.y + 1.5, b.w - 3, 5, 4)
    ctx.clip()
    ctx.fillStyle = accent
    ctx.fillRect(b.x + 1.5, b.y + 1.5, b.w - 3, 5)
    ctx.restore()
  }
}

function drawNode(
  ctx: CanvasRenderingContext2D,
  n: CircuitNode,
  selected: boolean,
  signal: SignalMap,
  chipColour: Record<string, string>,
  zoom: number,
) {
  const b = nodeBox(n)

  // ---------- INPUT (prominent toggle) ----------
  if (n.kind === 'INPUT') {
    drawBody(ctx, n, null, selected, zoom)
    const value = !!n.value
    const btnW = 42
    const btnH = 22
    const bx = n.position.x + NODE_W - btnW - 12
    const by = n.position.y + (b.h - btnH) / 2

    // button background
    ctx.fillStyle = value ? '#2563eb' : '#e2e8f0'
    roundRect(ctx, bx, by, btnW, btnH, 6)
    ctx.fill()
    ctx.strokeStyle = value ? '#1d4ed8' : '#94a3b8'
    ctx.lineWidth = 1.2
    ctx.stroke()

    // ON / OFF text
    ctx.fillStyle = value ? '#ffffff' : '#475569'
    ctx.font = '700 10px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'
    ctx.textBaseline = 'middle'
    ctx.fillText(value ? 'ON' : 'OFF', bx + btnW / 2, by + btnH / 2 + 0.5)

    // label
    ctx.fillStyle = LABEL
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'left'
    ctx.fillText(n.label, n.position.x + 12, n.position.y + b.h / 2)
    return
  }

  // ---------- OUTPUT (large LED) ----------
  if (n.kind === 'OUTPUT') {
    drawBody(ctx, n, null, selected, zoom)
    const value = !!signal[pinKey(n.id, n.inputs[0]?.id ?? 'in')]
    const cy = n.position.y + b.h / 2
    const cx = n.position.x + NODE_W - 26

    if (value) {
      ctx.save()
      ctx.shadowColor = 'rgba(37,99,235,0.55)'
      ctx.shadowBlur = 14
    }
    ctx.beginPath()
    ctx.arc(cx, cy, 11, 0, Math.PI * 2)
    ctx.fillStyle = value ? '#2563eb' : '#cbd5e1'
    ctx.fill()
    ctx.strokeStyle = value ? '#1d4ed8' : '#94a3b8'
    ctx.lineWidth = 1.5
    ctx.stroke()
    if (value) ctx.restore()

    // inner highlight
    if (value) {
      ctx.beginPath()
      ctx.arc(cx - 3, cy - 3, 3.5, 0, Math.PI * 2)
      ctx.fillStyle = 'rgba(255,255,255,0.55)'
      ctx.fill()
    }

    ctx.fillStyle = LABEL
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'left'
    ctx.textBaseline = 'middle'
    ctx.fillText(n.label, n.position.x + 12, cy)
    return
  }

  // ---------- CHIP ----------
  if (n.kind === 'CHIP') {
    const accent = (n.chipId ? chipColour[n.chipId] : null) ?? '#6366f1'
    drawBody(ctx, n, accent, selected, zoom)
    ctx.fillStyle = LABEL
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'
    ctx.textBaseline = 'middle'
    ctx.fillText(n.label, n.position.x + b.w / 2, n.position.y + b.h / 2 + 1)
    return
  }

  // ---------- gates ----------
  drawBody(ctx, n, null, selected, zoom)
  const cx = n.position.x + b.w / 2
  const cy = n.position.y + b.h / 2
  const glyph = n.kind === 'AND' ? '∧' : n.kind === 'OR' ? '∨' : '¬'
  ctx.fillStyle = BODY_EDGE
  ctx.font = '800 28px ui-sans-serif, system-ui, sans-serif'
  ctx.textAlign = 'center'
  ctx.textBaseline = 'middle'
  ctx.fillText(glyph, cx, cy + 1)
  ctx.fillStyle = '#475569'
  ctx.font = '600 10px ui-sans-serif, system-ui, sans-serif'
  ctx.fillText(n.label === '¬' ? 'NOT' : n.label, cx, n.position.y + 13)
}

function drawPin(
  ctx: CanvasRenderingContext2D,
  x: number, y: number, high: boolean, zoom: number,
) {
  ctx.beginPath()
  ctx.arc(x, y, PIN_R, 0, Math.PI * 2)
  ctx.fillStyle = high ? PIN_HIGH : '#e2e8f0'
  ctx.fill()
  ctx.strokeStyle = high ? '#1d4ed8' : PIN_LOW
  ctx.lineWidth = 1.3 / zoom
  ctx.stroke()
}

function wireView(from: CircuitNode, to: CircuitNode, w: Wire) {
  const fi = from.outputs.findIndex((p) => p.id === w.from.pinId)
  const ti = to.inputs.findIndex((p) => p.id === w.to.pinId)
  if (fi < 0 || ti < 0) return null
  return { path: cubic(rightPinPos(from, fi), leftPinPos(to, ti)) }
}

function drawScene(
  ctx: CanvasRenderingContext2D,
  sw: number, sh: number, dpr: number,
  cam: Camera,
  nodes: CircuitNode[], wires: Wire[],
  signal: SignalMap,
  selected: Set<string>,
  hoverWireId: string | null,
  chipColour: Record<string, string>,
  pending: { start: PinRef; startPos: Vec2; end: Vec2 } | null,
  box: { x: number; y: number; w: number; h: number } | null,
  placing: { x: number; y: number; label: string; colour: string } | null,
) {
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0)
  ctx.clearRect(0, 0, sw, sh)
  ctx.fillStyle = CANVAS_BG
  ctx.fillRect(0, 0, sw, sh)

  const { zoom, offsetX, offsetY } = cam
  ctx.setTransform(dpr * zoom, 0, 0, dpr * zoom, dpr * offsetX, dpr * offsetY)

  const wl = -offsetX / zoom
  const wt = -offsetY / zoom
  const wr = (sw - offsetX) / zoom
  const wb = (sh - offsetY) / zoom
  drawGrid(ctx, wl, wt, wr, wb, zoom)

  const byId = new Map(nodes.map((n) => [n.id, n]))
  const wireActive = (w: Wire) => !!signal[pinKey(w.from.nodeId, w.from.pinId)]

  for (const w of wires) {
    const from = byId.get(w.from.nodeId)
    const to = byId.get(w.to.nodeId)
    if (!from || !to) continue
    const vw = wireView(from, to, w)
    if (!vw) continue
    const high = wireActive(w)
    const hover = hoverWireId === w.id
    const p = vw.path
    if (high) {
      ctx.save()
      ctx.strokeStyle = 'rgba(37,99,235,0.18)'
      ctx.lineWidth = 7 / zoom
      ctx.beginPath()
      ctx.moveTo(p.a.x, p.a.y)
      ctx.bezierCurveTo(p.c1.x, p.c1.y, p.c2.x, p.c2.y, p.b.x, p.b.y)
      ctx.stroke()
      ctx.restore()
    }
    ctx.strokeStyle = hover ? WIRE_HOVER : high ? WIRE_HIGH : WIRE_LOW
    ctx.lineWidth = clamp(2.1 / zoom, 1.2, 2.6)
    if (hover) ctx.setLineDash([5 / zoom, 3 / zoom])
    ctx.beginPath()
    ctx.moveTo(p.a.x, p.a.y)
    ctx.bezierCurveTo(p.c1.x, p.c1.y, p.c2.x, p.c2.y, p.b.x, p.b.y)
    ctx.stroke()
    ctx.setLineDash([])
  }

  for (const n of nodes) drawNode(ctx, n, selected.has(n.id), signal, chipColour, zoom)

  for (const n of nodes) {
    for (const pin of enumeratePins(n)) {
      drawPin(ctx, pin.pos.x, pin.pos.y, !!signal[pinKey(pin.nodeId, pin.pinId)], zoom)
    }
  }

  if (pending) {
    ctx.strokeStyle = WIRE_HIGH
    ctx.setLineDash([5 / zoom, 4 / zoom])
    ctx.lineWidth = 1.9 / zoom
    const p = cubic(pending.startPos, pending.end)
    ctx.beginPath()
    ctx.moveTo(p.a.x, p.a.y)
    ctx.bezierCurveTo(p.c1.x, p.c1.y, p.c2.x, p.c2.y, p.b.x, p.b.y)
    ctx.stroke()
    ctx.setLineDash([])
    ctx.beginPath()
    ctx.arc(pending.end.x, pending.end.y, 3.8 / zoom, 0, Math.PI * 2)
    ctx.fillStyle = WIRE_HIGH
    ctx.fill()
  }

  if (placing) {
    ctx.globalAlpha = 0.72
    ctx.fillStyle = 'rgba(37,99,235,0.06)'
    ctx.strokeStyle = placing.colour
    ctx.lineWidth = 1.5
    roundRect(ctx, placing.x, placing.y, NODE_W, 58, 8)
    ctx.fill()
    ctx.stroke()
    ctx.fillStyle = LABEL
    ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif'
    ctx.textAlign = 'center'
    ctx.textBaseline = 'middle'
    ctx.fillText(placing.label, placing.x + NODE_W / 2, placing.y + 29)
    ctx.globalAlpha = 1
  }

  if (box && (Math.abs(box.w) > 2 || Math.abs(box.h) > 2)) {
    const rx = Math.min(box.x, box.x + box.w)
    const ry = Math.min(box.y, box.y + box.h)
    ctx.fillStyle = 'rgba(37,99,235,0.08)'
    ctx.strokeStyle = 'rgba(37,99,235,0.55)'
    ctx.lineWidth = 1 / zoom
    ctx.beginPath()
    ctx.rect(rx, ry, Math.abs(box.w), Math.abs(box.h))
    ctx.fill()
    ctx.stroke()
  }
}

/* ------------------------------------------------------------------ */
/* Persistence                                                         */
/* ------------------------------------------------------------------ */
const STORAGE_KEY = 'logiccraft.blueprint.v1'

interface SavedState {
  nodes: CircuitNode[]
  wires: Wire[]
  chips: ChipDefinition[]
  camera: Camera
}

function loadState(): Partial<SavedState> {
  try {
    const raw = localStorage.getItem(STORAGE_KEY)
    if (!raw) return {}
    return JSON.parse(raw)
  } catch {
    return {}
  }
}

function saveState(s: SavedState) {
  try {
    localStorage.setItem(
      STORAGE_KEY,
      JSON.stringify({ ...s, chips: s.chips.filter((c) => !c.builtin) }),
    )
  } catch { /* ignore */ }
}

/* ------------------------------------------------------------------ */
/* Main component                                                      */
/* ------------------------------------------------------------------ */
type DragMode =
  | { kind: 'move'; ids: string[]; startWorld: Vec2; origin: Map<string, Vec2> }
  | { kind: 'box'; startX: number; startY: number; endX: number; endY: number }
  | { kind: 'wire'; start: PinRef; startPos: Vec2; end: Vec2 }
  | null

interface PanState {
  startScreenX: number
  startScreenY: number
  startOffsetX: number
  startOffsetY: number
}

export default function LogicSimulator() {
  const saved = useMemo(() => loadState(), [])
  const [nodes, setNodes] = useState<CircuitNode[]>(saved.nodes ?? [])
  const [wires, setWires] = useState<Wire[]>(saved.wires ?? [])
  const [chips, setChips] = useState<ChipDefinition[]>(() => [
    ...makeBuiltInChips(),
    ...(saved.chips ?? []),
  ])
  const [selected, setSelected] = useState<Set<string>>(new Set())
  const [tool, setTool] = useState<Tool>('select')
  const [placement, setPlacement] = useState<Placement>(null)
  const [camera, setCamera] = useState<Camera>(
    saved.camera ?? { zoom: 1, offsetX: 40, offsetY: 40 },
  )
  const [editing, setEditing] = useState<EditSession | null>(null)
  const [createModal, setCreateModal] = useState(false)
  const [chipName, setChipName] = useState('My Chip')
  const [chipColor, setChipColor] = useState(CHIP_ACCENTS[0])
  const [history, setHistory] = useState<HistoryEntry[]>([])
  const [clipboard, setClipboard] = useState<{ nodes: CircuitNode[]; wires: Wire[] } | null>(null)
  const [, setFrameTick] = useState(0)

  const canvasRef = useRef<HTMLCanvasElement>(null)
  const drag = useRef<DragMode>(null)
  const pan = useRef<PanState | null>(null)
  const spaceDown = useRef(false)
  const pending = useRef<{ start: PinRef; startPos: Vec2 } | null>(null)
  const hoverWire = useRef<string | null>(null)
  const signal = useRef<SignalMap>({})
  const mousePos = useRef<Vec2>({ x: 0, y: 0 })
  const hasLoaded = useRef(false)
  const modalOpen = useRef(false)

  const live = useRef({ nodes, wires, chips, selected, placement, tool, camera })
  useEffect(() => {
    live.current = { nodes, wires, chips, selected, placement, tool, camera }
  })
  useEffect(() => {
    modalOpen.current = createModal
  }, [createModal])

  const simulator = useMemo(() => new Simulator(), [])
  const chipsById = useMemo(() => Object.fromEntries(chips.map((c) => [c.id, c])), [chips])
  const compiled = useMemo(
    () => compileCircuit({ nodes, wires }, chipsById),
    [nodes, wires, chipsById],
  )
  simulator.load(compiled)

  // persist
  useEffect(() => {
    if (!hasLoaded.current) {
      hasLoaded.current = true
      return
    }
    const t = setTimeout(() => saveState({ nodes, wires, chips, camera }), 350)
    return () => clearTimeout(t)
  }, [nodes, wires, chips, camera])

  // continuous simulation
  useEffect(() => {
    const id = setInterval(() => {
      simulator.tick(live.current.nodes)
      signal.current = simulator.snapshot()
      setFrameTick((t) => (t + 1) % 1_000_000)
    }, 1000 / SIM_TPS)
    return () => clearInterval(id)
  }, [simulator])

  /* history helpers */
  const pushHistory = useCallback(() => {
    setHistory((h) => {
      const entry: HistoryEntry = {
        nodes: live.current.nodes.map((n) => ({ ...n, position: { ...n.position } })),
        wires: live.current.wires.map((w) => ({ ...w })),
      }
      const next = [...h, entry]
      return next.length > 60 ? next.slice(-60) : next
    })
  }, [])

  const undo = useCallback(() => {
    setHistory((h) => {
      if (h.length === 0) return h
      const prev = h[h.length - 1]
      setNodes(prev.nodes)
      setWires(prev.wires)
      setSelected(new Set())
      return h.slice(0, -1)
    })
  }, [])

  /* helpers */
  const canvasRect = () => canvasRef.current!.getBoundingClientRect()
  const screenToWorld = (sx: number, sy: number): Vec2 => {
    const c = live.current.camera
    return { x: (sx - c.offsetX) / c.zoom, y: (sy - c.offsetY) / c.zoom }
  }
  const posFromEvent = (e: React.PointerEvent) => {
    const r = canvasRect()
    return screenToWorld(e.clientX - r.left, e.clientY - r.top)
  }

  const findPinAt = (p: Vec2) => {
    let best: EnumeratedPin | null = null
    let bestD = Infinity
    const grab = (PIN_R + 7) / live.current.camera.zoom
    for (const n of live.current.nodes) {
      for (const pin of enumeratePins(n)) {
        const d = Math.hypot(p.x - pin.pos.x, p.y - pin.pos.y)
        if (d < grab && d < bestD) {
          bestD = d
          best = pin
        }
      }
    }
    return best
  }

  const findNodeAt = (p: Vec2) => {
    for (let i = live.current.nodes.length - 1; i >= 0; i--) {
      if (hitNode(live.current.nodes[i], p)) return live.current.nodes[i]
    }
    return null
  }

  const findHoveredWire = (p: Vec2) => {
    const zoom = live.current.camera.zoom
    const byId = new Map(live.current.nodes.map((n) => [n.id, n]))
    let best: string | null = null
    let bestD = 13 / zoom
    for (const w of live.current.wires) {
      const from = byId.get(w.from.nodeId)
      const to = byId.get(w.to.nodeId)
      if (!from || !to) continue
      const vw = wireView(from, to, w)
      if (!vw) continue
      const mid = { x: (vw.path.a.x + vw.path.b.x) / 2, y: vw.path.a.y }
      const d = Math.min(
        distToSegment(p, vw.path.a, mid),
        distToSegment(p, mid, vw.path.b),
      )
      if (d < bestD) {
        bestD = d
        best = w.id
      }
    }
    return best
  }

  // Place centred under cursor
  const place = (p: Vec2) => {
    if (!placement) return
    pushHistory()
    const h = 58
    const snapped = { x: snap(p.x - NODE_W / 2), y: snap(p.y - h / 2) }
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
    setPlacement(null)
  }

  /* pointer handlers */
  const onPointerDown = (e: React.PointerEvent) => {
    const r = canvasRect()
    const sx = e.clientX - r.left
    const sy = e.clientY - r.top

    if (e.button === 1 || (e.button === 0 && spaceDown.current)) {
      e.preventDefault()
      canvasRef.current!.setPointerCapture(e.pointerId)
      pan.current = {
        startScreenX: sx,
        startScreenY: sy,
        startOffsetX: camera.offsetX,
        startOffsetY: camera.offsetY,
      }
      canvasRef.current!.style.cursor = 'grabbing'
      return
    }
    if (e.button === 2) return

    const p = screenToWorld(sx, sy)
    canvasRef.current!.setPointerCapture(e.pointerId)

    if (placement) {
      place(p)
      return
    }

    const pin = findPinAt(p)

    if (tool === 'wire' && pin) {
      if (pin.side === 'out') {
        drag.current = {
          kind: 'wire',
          start: { nodeId: pin.nodeId, pinId: pin.pinId, side: 'out' },
          startPos: pin.pos,
          end: pin.pos,
        }
      } else if (pin.side === 'in' && pending.current) {
        pushHistory()
        finishWire(pending.current.start, {
          nodeId: pin.nodeId,
          pinId: pin.pinId,
          side: 'in',
        })
        pending.current = null
      }
      return
    }

    if (tool === 'select') {
      if (pin && pin.side === 'out') {
        drag.current = {
          kind: 'wire',
          start: { nodeId: pin.nodeId, pinId: pin.pinId, side: 'out' },
          startPos: pin.pos,
          end: pin.pos,
        }
        return
      }
      if (pin && pin.side === 'in' && pending.current) {
        pushHistory()
        finishWire(pending.current.start, {
          nodeId: pin.nodeId,
          pinId: pin.pinId,
          side: 'in',
        })
        pending.current = null
        return
      }

      const node = findNodeAt(p)
      if (node) {
        // INPUT toggle hit
        if (node.kind === 'INPUT') {
          const btnW = 42
          const btnH = 22
          const bx = node.position.x + NODE_W - btnW - 12
          const by = node.position.y + (nodeHeight(node) - btnH) / 2
          if (p.x >= bx && p.x <= bx + btnW && p.y >= by && p.y <= by + btnH) {
            pushHistory()
            toggleInput(node.id)
            setSelected(new Set([node.id]))
            return
          }
        }
        const multi = e.shiftKey || selected.has(node.id)
        const next = new Set<string>(multi ? selected : [])
        next.add(node.id)
        setSelected(next)
        const origin = new Map<string, Vec2>()
        for (const n of live.current.nodes) {
          if (next.has(n.id)) origin.set(n.id, { ...n.position })
        }
        drag.current = { kind: 'move', ids: Array.from(next), startWorld: p, origin }
        return
      }

      setSelected(new Set())
      drag.current = { kind: 'box', startX: p.x, startY: p.y, endX: p.x, endY: p.y }
    }
  }

  const onPointerMove = (e: React.PointerEvent) => {
    const r = canvasRect()
    const sx = e.clientX - r.left
    const sy = e.clientY - r.top

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

    if (drag.current?.kind === 'box') {
      drag.current.endX = p.x
      drag.current.endY = p.y
    } else if (drag.current?.kind === 'wire') {
      drag.current.end = p
    } else if (drag.current?.kind === 'move') {
      const d = drag.current
      const dx = p.x - d.startWorld.x
      const dy = p.y - d.startWorld.y
      const idSet = new Set(d.ids)
      setNodes((ns) =>
        ns.map((n) =>
          idSet.has(n.id)
            ? {
              ...n,
              position: {
                x: d.origin.get(n.id)!.x + dx,
                y: d.origin.get(n.id)!.y + dy,
              },
            }
            : n,
        ),
      )
    } else {
      hoverWire.current = findHoveredWire(p)
    }
  }

  const onPointerUp = (e: React.PointerEvent) => {
    if (pan.current) {
      pan.current = null
      if (canvasRef.current)
        canvasRef.current.style.cursor = spaceDown.current ? 'grab' : 'default'
      return
    }
    const p = posFromEvent(e)
    const d = drag.current
    if (d?.kind === 'box') {
      const minX = Math.min(d.startX, d.endX)
      const maxX = Math.max(d.startX, d.endX)
      const minY = Math.min(d.startY, d.endY)
      const maxY = Math.max(d.startY, d.endY)
      const next = new Set<string>()
      for (const n of live.current.nodes) {
        const b = nodeBox(n)
        if (b.x < maxX && b.x + b.w > minX && b.y < maxY && b.y + b.h > minY)
          next.add(n.id)
      }
      setSelected(next)
    } else if (d?.kind === 'wire') {
      const pin = findPinAt(p)
      if (pin && pin.side === 'in') {
        pushHistory()
        finishWire(d.start, { nodeId: pin.nodeId, pinId: pin.pinId, side: 'in' })
        pending.current = null
      } else {
        pending.current = { start: d.start, startPos: d.startPos }
      }
    } else if (d?.kind === 'move') {
      // snap positions on drop
      const idSet = new Set(d.ids)
      setNodes((ns) =>
        ns.map((n) =>
          idSet.has(n.id)
            ? { ...n, position: { x: snap(n.position.x), y: snap(n.position.y) } }
            : n,
        ),
      )
    }
    drag.current = null
  }

  const finishWire = (from: PinRef, to: PinRef) => {
    if (isPinRefEqual(from, to) || from.nodeId === to.nodeId) return
    setWires((ws) => {
      const filtered = ws.filter((w) => !isPinRefEqual(w.to, to))
      return [...filtered, createWire(from, to)]
    })
  }

  const deleteSelection = () => {
    if (selected.size === 0) return
    pushHistory()
    const ids = new Set(selected)
    setNodes((ns) => ns.filter((n) => !ids.has(n.id)))
    setWires((ws) =>
      ws.filter((w) => !ids.has(w.from.nodeId) && !ids.has(w.to.nodeId)),
    )
    setSelected(new Set())
  }

  const toggleInput = (id: string) => {
    setNodes((ns) =>
      ns.map((n) => (n.id === id && n.kind === 'INPUT' ? { ...n, value: !n.value } : n)),
    )
  }

  /* copy / paste */
  const copySelection = () => {
    if (selected.size === 0) return
    const ids = new Set(selected)
    const selNodes = nodes.filter((n) => ids.has(n.id)).map((n) => ({
      ...n,
      position: { ...n.position },
    }))
    const selWires = wires.filter(
      (w) => ids.has(w.from.nodeId) && ids.has(w.to.nodeId),
    )
    setClipboard({ nodes: selNodes, wires: selWires })
  }

  const pasteClipboard = () => {
    if (!clipboard || clipboard.nodes.length === 0) return
    pushHistory()
    const idMap = new Map<string, string>()
    const offset = 40
    const newNodes = clipboard.nodes.map((n) => {
      const newId = uid(n.kind.toLowerCase())
      idMap.set(n.id, newId)
      return {
        ...n,
        id: newId,
        position: { x: n.position.x + offset, y: n.position.y + offset },
      }
    })
    const newWires = clipboard.wires.map((w) => ({
      id: uid('w'),
      from: {
        ...w.from,
        nodeId: idMap.get(w.from.nodeId)!,
      },
      to: {
        ...w.to,
        nodeId: idMap.get(w.to.nodeId)!,
      },
    }))
    setNodes((ns) => [...ns, ...newNodes])
    setWires((ws) => [...ws, ...newWires])
    setSelected(new Set(newNodes.map((n) => n.id)))
  }

  /* chip creation */
  const openCreateModal = () => {
    if (selected.size === 0) return
    setChipName('My Chip')
    setChipColor(CHIP_ACCENTS[Math.floor(Math.random() * CHIP_ACCENTS.length)])
    setCreateModal(true)
  }

  const confirmCreateChip = () => {
    const def = packageSelectionInto(
      chipName.trim() || 'My Chip',
      chipColor,
      live.current.nodes,
      live.current.wires,
      live.current.selected,
    )
    if (!def) {
      window.alert('Selection must contain at least one INPUT and one OUTPUT.')
      return
    }
    pushHistory()
    setChips((cs) => [...cs, def])
    const ids = new Set(def.nodes.map((n) => n.id))
    const instance = createChipNode(def, centroidOf(def.nodes))
    setNodes((ns) => [...ns.filter((n) => !ids.has(n.id)), instance])
    setWires((ws) =>
      ws.filter((w) => !ids.has(w.from.nodeId) && !ids.has(w.to.nodeId)),
    )
    setSelected(new Set([instance.id]))
    setCreateModal(false)
  }

  /* edit mode */
  const enterEditChip = (chipId: string) => {
    if (editing) return
    const chip = chipsById[chipId]
    if (!chip || chip.builtin) return
    setEditing({
      chipId,
      snapNodes: live.current.nodes,
      snapWires: live.current.wires,
      snapSelected: live.current.selected,
      snapCamera: live.current.camera,
    })
    setNodes(chip.nodes.map((n) => ({ ...n, position: { ...n.position } })))
    setWires(chip.wires.map((w) => ({ ...w })))
    setSelected(new Set())
    setPlacement(null)
    pending.current = null
    setCamera({ zoom: 1, offsetX: 40, offsetY: 40 })
  }

  const exitEditChip = (save: boolean) => {
    setEditing((session) => {
      if (!session) return null
      if (save) {
        const curNodes = live.current.nodes
        const curWires = live.current.wires
        const inputs = curNodes
          .filter((n) => n.kind === 'INPUT')
          .sort((a, b) => a.position.y - b.position.y)
        const outputs = curNodes
          .filter((n) => n.kind === 'OUTPUT')
          .sort((a, b) => a.position.y - b.position.y)
        if (inputs.length === 0 || outputs.length === 0) {
          window.alert('A chip needs at least one INPUT and one OUTPUT.')
          return session
        }
        const chip = chipsById[session.chipId]
        const updated: ChipDefinition = {
          ...chip,
          nodes: curNodes,
          wires: curWires,
          inputNodeIds: inputs.map((n) => n.id),
          outputNodeIds: outputs.map((n) => n.id),
        }
        setChips((cs) => cs.map((c) => (c.id === session.chipId ? updated : c)))

        const validIn = new Set(updated.inputNodeIds.map((_, i) => `i${i}`))
        const validOut = new Set(updated.outputNodeIds.map((_, i) => `o${i}`))
        const refreshed = session.snapNodes.map((n) =>
          n.kind === 'CHIP' && n.chipId === session.chipId
            ? refreshChipInstance(n, updated)
            : n,
        )
        const refreshedIds = new Set(
          refreshed.filter((n) => n.chipId === session.chipId).map((n) => n.id),
        )
        const refreshedWires = session.snapWires.filter((w) => {
          const fromStale =
            refreshedIds.has(w.from.nodeId) && !validOut.has(w.from.pinId)
          const toStale =
            refreshedIds.has(w.to.nodeId) && !validIn.has(w.to.pinId)
          return !fromStale && !toStale
        })
        setNodes(refreshed)
        setWires(refreshedWires)
      } else {
        setNodes(session.snapNodes)
        setWires(session.snapWires)
      }
      setSelected(session.snapSelected)
      setCamera(session.snapCamera)
      setPlacement(null)
      pending.current = null
      return null
    })
  }

  const deleteCustomChip = (chipId: string) => {
    const chip = chipsById[chipId]
    if (!chip || chip.builtin) return
    if (!window.confirm(`Delete “${chip.name}”? All instances will be removed.`))
      return
    pushHistory()
    const remove = new Set(
      live.current.nodes.filter((n) => n.chipId === chipId).map((n) => n.id),
    )
    setChips((cs) => cs.filter((c) => c.id !== chipId))
    setNodes((ns) => ns.filter((n) => !remove.has(n.id)))
    setWires((ws) =>
      ws.filter((w) => !remove.has(w.from.nodeId) && !remove.has(w.to.nodeId)),
    )
    setSelected((s) => {
      const next = new Set(s)
      remove.forEach((id) => next.delete(id))
      return next
    })
    if (placement?.type === 'CHIP' && placement.chipId === chipId)
      setPlacement(null)
  }

  const onDoubleClick = (e: React.MouseEvent) => {
    if (editing || placement) return
    const r = canvasRect()
    const p = screenToWorld(e.clientX - r.left, e.clientY - r.top)
    const node = findNodeAt(p)
    if (
      node?.kind === 'CHIP' &&
      node.chipId &&
      !chipsById[node.chipId]?.builtin
    ) {
      enterEditChip(node.chipId)
    }
  }

  const onContextMenu = (e: React.PointerEvent) => {
    e.preventDefault()
    const p = posFromEvent(e)
    const hw = findHoveredWire(p)
    if (hw) {
      pushHistory()
      setWires((ws) => ws.filter((w) => w.id !== hw))
    } else if (selected.size > 0) {
      deleteSelection()
    }
  }

  const clearAll = () => {
    if (editing) return
    pushHistory()
    setNodes([])
    setWires([])
    setSelected(new Set())
    setPlacement(null)
    pending.current = null
    simulator.reset()
    signal.current = {}
  }

  const resetView = () => setCamera({ zoom: 1, offsetX: 40, offsetY: 40 })

  /* export / import */
  const exportJSON = () => {
    const data = {
      version: 1,
      nodes,
      wires,
      chips: chips.filter((c) => !c.builtin),
      camera,
    }
    const blob = new Blob([JSON.stringify(data, null, 2)], {
      type: 'application/json',
    })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = `logiccraft-${Date.now()}.json`
    a.click()
    URL.revokeObjectURL(url)
  }

  const importJSON = () => {
    const input = document.createElement('input')
    input.type = 'file'
    input.accept = '.json,application/json'
    input.onchange = async () => {
      const file = input.files?.[0]
      if (!file) return
      try {
        const text = await file.text()
        const data = JSON.parse(text)
        if (!Array.isArray(data.nodes) || !Array.isArray(data.wires))
          throw new Error('Invalid')
        pushHistory()
        setNodes(data.nodes)
        setWires(data.wires)
        setChips([...makeBuiltInChips(), ...(data.chips ?? [])])
        if (data.camera) setCamera(data.camera)
        setSelected(new Set())
        setPlacement(null)
        pending.current = null
      } catch {
        window.alert('Could not import file.')
      }
    }
    input.click()
  }

  /* keyboard */
  useEffect(() => {
    const down = (e: KeyboardEvent) => {
      // never steal keys while typing in modal / inputs
      if (
        modalOpen.current ||
        (e.target as HTMLElement)?.tagName === 'INPUT' ||
        (e.target as HTMLElement)?.tagName === 'TEXTAREA'
      ) {
        return
      }

      if (e.code === 'Space') {
        if (!spaceDown.current) {
          spaceDown.current = true
          if (canvasRef.current && !pan.current)
            canvasRef.current.style.cursor = 'grab'
        }
        e.preventDefault()
        return
      }

      const mod = e.metaKey || e.ctrlKey

      if (mod && e.key === 'z') {
        e.preventDefault()
        undo()
        return
      }
      if (mod && e.key === 'c') {
        e.preventDefault()
        copySelection()
        return
      }
      if (mod && e.key === 'v') {
        e.preventDefault()
        pasteClipboard()
        return
      }

      if (e.key === 'Escape') {
        pending.current = null
        setPlacement(null)
        setCreateModal(false)
      }
      if ((e.key === 'Delete' || e.key === 'Backspace') && live.current.selected.size > 0) {
        e.preventDefault()
        deleteSelection()
      }
    }
    const up = (e: KeyboardEvent) => {
      if (e.code === 'Space') {
        spaceDown.current = false
        if (canvasRef.current && !pan.current)
          canvasRef.current.style.cursor = 'default'
      }
    }
    window.addEventListener('keydown', down)
    window.addEventListener('keyup', up)
    return () => {
      window.removeEventListener('keydown', down)
      window.removeEventListener('keyup', up)
    }
  }, [undo])

  /* wheel zoom */
  useEffect(() => {
    const canvas = canvasRef.current
    if (!canvas) return
    const onWheel = (e: WheelEvent) => {
      e.preventDefault()
      const r = canvas.getBoundingClientRect()
      const sx = e.clientX - r.left
      const sy = e.clientY - r.top
      setCamera((cam) => {
        const factor = Math.exp(-e.deltaY * 0.0011)
        const newZoom = clamp(cam.zoom * factor, MIN_ZOOM, MAX_ZOOM)
        const wx = (sx - cam.offsetX) / cam.zoom
        const wy = (sy - cam.offsetY) / cam.zoom
        return {
          zoom: newZoom,
          offsetX: sx - wx * newZoom,
          offsetY: sy - wy * newZoom,
        }
      })
    }
    canvas.addEventListener('wheel', onWheel, { passive: false })
    return () => canvas.removeEventListener('wheel', onWheel)
  }, [])

  /* render loop */
  useEffect(() => {
    let raf = 0
    const loop = () => {
      raf = requestAnimationFrame(loop)
      const canvas = canvasRef.current
      if (!canvas) return
      const dpr = window.devicePixelRatio || 1
      const ctx = canvas.getContext('2d')
      if (!ctx) return
      const cw = canvas.clientWidth
      const ch = canvas.clientHeight
      if (
        canvas.width !== Math.round(cw * dpr) ||
        canvas.height !== Math.round(ch * dpr)
      ) {
        canvas.width = Math.round(cw * dpr)
        canvas.height = Math.round(ch * dpr)
      }

      const s = live.current
      const box =
        drag.current?.kind === 'box'
          ? {
            x: drag.current.startX,
            y: drag.current.startY,
            w: drag.current.endX - drag.current.startX,
            h: drag.current.endY - drag.current.startY,
          }
          : null

      let pnd: { start: PinRef; startPos: Vec2; end: Vec2 } | null = null
      if (drag.current?.kind === 'wire') {
        pnd = {
          start: drag.current.start,
          startPos: drag.current.startPos,
          end: drag.current.end,
        }
      } else if (pending.current) {
        pnd = {
          start: pending.current.start,
          startPos: pending.current.startPos,
          end: mousePos.current,
        }
      }

      const chipColour: Record<string, string> = {}
      for (const c of s.chips) chipColour[c.id] = c.color

      const placing = s.placement
        ? {
          x: snap(mousePos.current.x - NODE_W / 2),
          y: snap(mousePos.current.y - 29),
          label:
            s.placement.type === 'CHIP'
              ? s.chips.find((c) => c.id === s.placement!.chipId)?.name ?? 'Chip'
              : s.placement.kind,
          colour:
            s.placement.type === 'CHIP'
              ? s.chips.find((c) => c.id === s.placement!.chipId)?.color ??
              '#2563eb'
              : '#1e293b',
        }
        : null

      drawScene(
        ctx,
        cw,
        ch,
        dpr,
        s.camera,
        s.nodes,
        s.wires,
        signal.current,
        s.selected,
        hoverWire.current,
        chipColour,
        pnd,
        box,
        placing,
      )
    }
    loop()
    return () => cancelAnimationFrame(raf)
  }, [])

  /* UI */
  const btn =
    'inline-flex flex-col items-center gap-0.5 rounded-md px-2.5 py-1.5 text-[11px] font-medium transition select-none'
  const active =
    'bg-blue-100 text-blue-700 ring-1 ring-blue-400/60'
  const idle = 'text-slate-600 hover:bg-slate-100 hover:text-slate-900'
  const isPrim = (k: PrimitiveType) =>
    placement?.type === 'PRIMITIVE' && placement.kind === k
  const isChip = (id: string) =>
    placement?.type === 'CHIP' && placement.chipId === id

  const builtinChips = chips.filter((c) => c.builtin)
  const customChips = chips.filter((c) => !c.builtin)
  const editingChip = editing ? chipsById[editing.chipId] : null

  return (
    <div className="flex h-screen w-screen flex-col overflow-hidden bg-slate-100 text-slate-800">
      {/* Top bar */}
      <header className="flex h-11 shrink-0 items-center gap-2 border-b border-slate-200 bg-white px-3 shadow-sm">
        <div className="mr-1 flex items-center gap-1.5">
          <span className="grid h-6 w-6 place-items-center rounded bg-slate-800 text-xs text-white">
            ⊼
          </span>
          <span className="text-sm font-bold tracking-tight text-slate-800">
            logic<span className="text-blue-600">craft</span>
          </span>
        </div>

        {editingChip ? (
          <div className="flex flex-1 items-center gap-2">
            <span className="rounded bg-slate-100 px-2 py-0.5 text-xs text-slate-600 ring-1 ring-slate-200">
              Editing{' '}
              <span className="font-semibold" style={{ color: editingChip.color }}>
                {editingChip.name}
              </span>
            </span>
            <span className="hidden text-[11px] text-slate-400 sm:inline">
              INPUT switches are live — test the circuit here.
            </span>
            <div className="flex-1" />
            <button
              onClick={() => exitEditChip(false)}
              className={`${btn} text-slate-500 hover:bg-slate-100`}
            >
              Cancel
            </button>
            <button
              onClick={() => exitEditChip(true)}
              className={`${btn} bg-emerald-50 text-emerald-700 hover:bg-emerald-100`}
            >
              Save & Close
            </button>
          </div>
        ) : (
          <>
            <div className="flex items-center gap-0.5 rounded-md bg-slate-50 p-0.5 ring-1 ring-slate-200">
              {(['select', 'wire'] as Tool[]).map((t) => (
                <button
                  key={t}
                  onClick={() => setTool(t)}
                  className={`${btn} px-2 ${tool === t ? active : idle}`}
                >
                  {t === 'select' ? '◆ Select' : '⌁ Wire'}
                </button>
              ))}
            </div>

            <div className="mx-1 h-5 w-px bg-slate-200" />

            <button
              onClick={openCreateModal}
              disabled={selected.size === 0}
              className={`${btn} ${selected.size === 0
                  ? 'cursor-not-allowed text-slate-300'
                  : 'bg-emerald-50 text-emerald-700 hover:bg-emerald-100'
                }`}
            >
              ⬒ Create Chip
            </button>

            <div className="mx-1 h-5 w-px bg-slate-200" />

            <button onClick={exportJSON} className={`${btn} ${idle}`} title="Export JSON">
              ↥ Export
            </button>
            <button onClick={importJSON} className={`${btn} ${idle}`} title="Import JSON">
              ↧ Import
            </button>

            <div className="mx-1 h-5 w-px bg-slate-200" />

            <button onClick={resetView} className={`${btn} ${idle}`} title="Reset view">
              ⤾
            </button>
            <span className="font-mono text-[11px] text-slate-400">
              {Math.round(camera.zoom * 100)}%
            </span>

            <div className="flex-1" />

            <span className="hidden text-[11px] text-slate-400 md:inline">
              {nodes.length} nodes · {wires.length} wires
            </span>

            <button
              onClick={clearAll}
              className={`${btn} text-slate-500 hover:bg-red-50 hover:text-red-600`}
            >
              ⌫ Clear
            </button>
          </>
        )}
      </header>

      {/* Canvas */}
      <main className="relative min-h-0 flex-1">
        <canvas
          ref={canvasRef}
          className="h-full w-full touch-none select-none"
          style={{ cursor: 'default' }}
          onPointerDown={onPointerDown}
          onPointerMove={onPointerMove}
          onPointerUp={onPointerUp}
          onPointerCancel={onPointerUp}
          onDoubleClick={onDoubleClick}
          onContextMenu={onContextMenu}
        />
        <div className="pointer-events-none absolute bottom-2 left-1/2 z-10 -translate-x-1/2 whitespace-nowrap rounded-md bg-white/90 px-3 py-1 text-[11px] text-slate-500 shadow-sm ring-1 ring-slate-200">
          {placement
            ? 'Click to place · Esc to cancel'
            : pending.current
              ? 'Click an input pin to finish the wire'
              : 'Scroll = zoom · Space/middle-drag = pan · Drag output pin = wire · ⌘/Ctrl+Z = undo · ⌘/Ctrl+C/V = copy/paste'}
        </div>
      </main>

      {/* Bottom palette */}
      {!editingChip && (
        <footer className="z-20 flex shrink-0 items-stretch gap-4 overflow-x-auto border-t border-slate-200 bg-white px-3 py-2 shadow-[0_-1px_3px_rgba(0,0,0,0.04)]">
          {/* I/O */}
          <section className="flex flex-col">
            <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider text-slate-400">
              I/O
            </h3>
            <div className="flex gap-1.5">
              {(['INPUT', 'OUTPUT'] as PrimitiveType[]).map((k) => (
                <button
                  key={k}
                  onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
                  className={`${btn} ${isPrim(k) ? active : idle}`}
                >
                  <span className="grid h-7 w-7 place-items-center rounded bg-slate-100 font-mono text-xs font-bold text-slate-700 ring-1 ring-slate-200">
                    {k === 'INPUT' ? 'I' : 'O'}
                  </span>
                  {k === 'INPUT' ? 'Toggle' : 'LED'}
                </button>
              ))}
            </div>
          </section>

          <div className="my-1 w-px bg-slate-200" />

          {/* Gates */}
          <section className="flex flex-col">
            <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider text-slate-400">
              Gates
            </h3>
            <div className="flex gap-1.5">
              {(['AND', 'OR', 'NOT'] as PrimitiveType[]).map((k) => (
                <button
                  key={k}
                  onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
                  className={`${btn} ${isPrim(k) ? active : idle}`}
                >
                  <span className="grid h-7 w-7 place-items-center rounded bg-slate-100 font-mono text-sm font-bold text-slate-700 ring-1 ring-slate-200">
                    {k === 'AND' ? '∧' : k === 'OR' ? '∨' : '¬'}
                  </span>
                  {k}
                </button>
              ))}
            </div>
          </section>

          <div className="my-1 w-px bg-slate-200" />

          {/* Flip-flops */}
          <section className="flex flex-col">
            <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider text-slate-400">
              Flip-Flops
            </h3>
            <div className="flex gap-1.5">
              {builtinChips.map((c) => (
                <button
                  key={c.id}
                  onClick={() => setPlacement({ type: 'CHIP', chipId: c.id })}
                  className={`${btn} ${isChip(c.id) ? active : idle}`}
                >
                  <span
                    className="grid h-7 min-w-7 place-items-center rounded bg-slate-100 px-1 font-mono text-xs font-bold ring-1"
                    style={{ color: c.color, borderColor: `${c.color}55` }}
                  >
                    {c.name.slice(0, 2).toUpperCase()}
                  </span>
                  <span className="max-w-20 truncate">{c.name}</span>
                </button>
              ))}
            </div>
          </section>

          {/* Custom */}
          {customChips.length > 0 && (
            <>
              <div className="my-1 w-px bg-slate-200" />
              <section className="flex min-w-0 flex-col">
                <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider text-slate-400">
                  Custom
                </h3>
                <div className="flex gap-1.5 overflow-x-auto">
                  {customChips.map((c) => (
                    <div key={c.id} className="group relative flex flex-col items-center">
                      <button
                        onClick={() => setPlacement({ type: 'CHIP', chipId: c.id })}
                        className={`${btn} ${isChip(c.id) ? active : idle}`}
                      >
                        <span
                          className="grid h-7 min-w-7 place-items-center rounded bg-slate-100 px-1 font-mono text-xs font-bold ring-1"
                          style={{ color: c.color, borderColor: `${c.color}55` }}
                        >
                          {c.name.slice(0, 2).toUpperCase()}
                        </span>
                        <span className="max-w-20 truncate">{c.name}</span>
                      </button>
                      <div className="absolute -top-1 right-0 hidden gap-0.5 group-hover:flex">
                        <button
                          onClick={(e) => {
                            e.stopPropagation()
                            enterEditChip(c.id)
                          }}
                          className="rounded bg-white px-1 text-[9px] text-slate-500 shadow ring-1 ring-slate-200 hover:text-slate-800"
                          title="Edit"
                        >
                          ✎
                        </button>
                        <button
                          onClick={(e) => {
                            e.stopPropagation()
                            deleteCustomChip(c.id)
                          }}
                          className="rounded bg-white px-1 text-[9px] text-red-500 shadow ring-1 ring-slate-200 hover:text-red-600"
                          title="Delete"
                        >
                          ✕
                        </button>
                      </div>
                    </div>
                  ))}
                </div>
              </section>
            </>
          )}
        </footer>
      )}

      {/* Create-chip modal */}
      {createModal && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-slate-900/30 backdrop-blur-[2px]">
          <div className="w-80 rounded-xl border border-slate-200 bg-white p-5 shadow-xl">
            <h2 className="mb-3 text-sm font-semibold text-slate-800">
              Create Custom Chip
            </h2>
            <label className="mb-1 block text-[11px] font-medium text-slate-500">
              Name
            </label>
            <input
              autoFocus
              value={chipName}
              onChange={(e) => setChipName(e.target.value)}
              onKeyDown={(e) => {
                if (e.key === 'Enter') confirmCreateChip()
                if (e.key === 'Escape') setCreateModal(false)
              }}
              className="mb-4 w-full rounded-md border border-slate-200 bg-slate-50 px-2.5 py-1.5 text-sm text-slate-800 outline-none focus:border-blue-400 focus:ring-2 focus:ring-blue-100"
            />
            <label className="mb-1.5 block text-[11px] font-medium text-slate-500">
              Accent colour
            </label>
            <div className="mb-5 flex flex-wrap gap-2">
              {CHIP_ACCENTS.map((c) => (
                <button
                  key={c}
                  onClick={() => setChipColor(c)}
                  className={`h-7 w-7 rounded-full ring-2 transition ${chipColor === c ? 'ring-slate-800 ring-offset-1' : 'ring-transparent'
                    }`}
                  style={{ background: c }}
                />
              ))}
            </div>
            <div className="flex justify-end gap-2">
              <button
                onClick={() => setCreateModal(false)}
                className={`${btn} text-slate-500 hover:bg-slate-100`}
              >
                Cancel
              </button>
              <button
                onClick={confirmCreateChip}
                className={`${btn} bg-blue-50 text-blue-700 hover:bg-blue-100`}
              >
                Create
              </button>
            </div>
          </div>
        </div>
      )}
    </div>
  )
}