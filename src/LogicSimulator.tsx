import { useEffect, useMemo, useRef, useState } from 'react'

/* =====================================================================
 *  TopCraft — Digital Logic Simulator
 *  -------------------------------------------------------------------
 *  A single-file, self-contained digital logic simulator inspired by
 *  Sebastian Lague's "Digital Logic Sim", rewritten from scratch for
 *  React 18/19 + Tailwind CSS.
 *
 *  Design decisions:
 *  - The canvas coordinate system is 1:1 with screen space (no zoom /
 *    pan), so every drag + wiring hit test is pure pixel math and never
 *    drifts from the pointer.
 *  - External connections are defined ONLY through explicit Input
 *    (toggle switch) and Output (LED) components.
 *  - Built-in and user-created blocks ("chips") are flattened into a
 *    netlist of primitive gates at compile time, and every chip instance
 *    gets its own prefixed copy of the internal graph, so instances have
 *    fully isolated internal logic (e.g. two RS latches never share
 *    state).
 *  - The simulation settles synchronously (all gates read the previous
 *    state, then commit together) which makes cross-coupled feedback
 *    like an RS latch behave correctly while a bounded settle loop keeps
 *    oscillators from freezing the browser.
 * ===================================================================== */

/* =====================================================================
 *  DATA MODEL
 * ===================================================================== */

type PinSide = 'in' | 'out'

interface Vec2 {
  x: number
  y: number
}

/** A fully-qualified reference to one pin of one node. */
interface PinRef {
  nodeId: string
  pinId: string
  side: PinSide
}

type PrimitiveType = 'AND' | 'OR' | 'NOT' | 'INPUT' | 'OUTPUT'
type NodeKind = PrimitiveType | 'CHIP'

interface Pin {
  id: string
  name: string
}

interface CircuitNode {
  id: string
  kind: NodeKind
  /** Only set when kind === 'CHIP' -> ChipDefinition.id */
  chipId?: string
  label: string
  position: Vec2
  inputs: Pin[]
  outputs: Pin[]
  /** Only meaningful for INPUT nodes: the logic level. */
  value?: boolean
}

interface Wire {
  id: string
  /** Must be an output pin. */
  from: PinRef
  /** Must be an input pin. */
  to: PinRef
}

interface ChipDefinition {
  id: string
  name: string
  color: string
  /** True for latches shipped with the app (always kept in the palette). */
  builtin?: boolean
  /** Internal graph. Its INPUT nodes become left pins, OUTPUT nodes right pins. */
  nodes: CircuitNode[]
  wires: Wire[]
  /** Ordered ids of the internal INPUT nodes, mapped to external input pins. */
  inputNodeIds: string[]
  /** Ordered ids of the internal OUTPUT nodes, mapped to external output pins. */
  outputNodeIds: string[]
}

/** `"<nodeId>:<pinId>"` -> logic level, used purely for rendering. */
type SignalMap = Record<string, boolean>

type Tool = 'select' | 'wire'
type Placement =
  | { type: 'PRIMITIVE'; kind: PrimitiveType }
  | { type: 'CHIP'; chipId: string }
  | null

const pinKey = (nodeId: string, pinId: string) => `${nodeId}:${pinId}`
const isPinRefEqual = (a: PinRef, b: PinRef) =>
  a.nodeId === b.nodeId && a.pinId === b.pinId && a.side === b.side
/* =====================================================================
 *  GEOMETRY (pixels; 1:1 with screen space)
 * ===================================================================== */

const GRID = 24
const NODE_W = 96
const NODE_PAD = 10
const PIN_SPACING = 22
const PIN_R = 5
const SWITCH_W = 30

let idCounter = 0
/** Short, collision-free id generator. */
const uid = (prefix = 'n') =>
  `${prefix}_${(idCounter++).toString(36)}_${Math.random().toString(36).slice(2, 7)}`

const nodeRows = (node: CircuitNode) =>
  Math.max(node.inputs.length, node.outputs.length, 1)

const nodeHeight = (node: CircuitNode) =>
  NODE_PAD * 2 + PIN_SPACING * Math.max(nodeRows(node) - 1, 0) + PIN_SPACING

const nodeBox = (node: CircuitNode) => ({
  x: node.position.x,
  y: node.position.y,
  w: NODE_W,
  h: nodeHeight(node),
})

const leftPinPos = (node: CircuitNode, index: number): Vec2 => ({
  x: node.position.x,
  y: node.position.y + NODE_PAD + PIN_SPACING / 2 + index * PIN_SPACING,
})

const rightPinPos = (node: CircuitNode, index: number): Vec2 => ({
  x: node.position.x + NODE_W,
  y: node.position.y + NODE_PAD + PIN_SPACING / 2 + index * PIN_SPACING,
})

interface EnumeratedPin {
  nodeId: string
  pinId: string
  side: PinSide
  index: number
  pos: Vec2
  node: CircuitNode
}

const enumeratePins = (node: CircuitNode): EnumeratedPin[] => {
  const list: EnumeratedPin[] = []
  node.inputs.forEach((pin, i) =>
    list.push({
      nodeId: node.id,
      pinId: pin.id,
      side: 'in',
      index: i,
      pos: leftPinPos(node, i),
      node,
    }),
  )
  node.outputs.forEach((pin, i) =>
    list.push({
      nodeId: node.id,
      pinId: pin.id,
      side: 'out',
      index: i,
      pos: rightPinPos(node, i),
      node,
    }),
  )
  return list
}

const hitNode = (node: CircuitNode, p: Vec2): boolean => {
  const b = nodeBox(node)
  return p.x >= b.x && p.x <= b.x + b.w && p.y >= b.y && p.y <= b.y + b.h
}

/** Distance from a point to a segment (used for selecting wires). */
const distToSegment = (p: Vec2, a: Vec2, b: Vec2): number => {
  const dx = b.x - a.x
  const dy = b.y - a.y
  const l2 = dx * dx + dy * dy
  if (l2 === 0) return Math.hypot(p.x - a.x, p.y - a.y)
  let t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / l2
  t = Math.max(0, Math.min(1, t))
  return Math.hypot(p.x - (a.x + t * dx), p.y - (a.y + t * dy))
}

const snap = (v: number) => Math.round(v / GRID) * GRID

/** The base point of the toggle-switch handle on an INPUT node. */
const inputKnobPos = (node: CircuitNode): Vec2 => ({
  x: node.position.x + NODE_W - SWITCH_W - 26 + 6,
  y: node.position.y + NODE_PAD + PIN_SPACING / 2,
})

/* =====================================================================
 *  FACTORY
 * ===================================================================== */

const PRIMITIVE_SPEC: Record<
  PrimitiveType,
  { label: string; inputs: string[]; outputs: string[] }
> = {
  AND: { label: 'AND', inputs: ['A', 'B'], outputs: ['OUT'] },
  OR: { label: 'OR', inputs: ['A', 'B'], outputs: ['OUT'] },
  NOT: { label: 'NOT', inputs: ['IN'], outputs: ['OUT'] },
  INPUT: { label: 'INPUT', inputs: [], outputs: ['OUT'] },
  OUTPUT: { label: 'OUTPUT', inputs: ['IN'], outputs: [] },
}

const makePins = (names: string[]): Pin[] =>
  names.map((name) => ({ id: name.toLowerCase(), name }))

function createPrimitiveNode(
  kind: PrimitiveType,
  position: Vec2,
  label?: string,
): CircuitNode {
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

/** The label of an internal node, looked up inside a chip definition. */
function labelOfNode(nodes: CircuitNode[], id: string): string {
  return nodes.find((n) => n.id === id)?.label ?? ''
}

/** An instance node for a packaged / built-in chip definition. */
function createChipNode(chip: ChipDefinition, position: Vec2): CircuitNode {
  return {
    id: uid('chip'),
    kind: 'CHIP',
    chipId: chip.id,
    label: chip.name,
    position,
    inputs: chip.inputNodeIds.map((nodeId, i) => ({
      id: `i${i}`,
      name: labelOfNode(chip.nodes, nodeId) || `IN${i}`,
    })),
    outputs: chip.outputNodeIds.map((nodeId, i) => ({
      id: `o${i}`,
      name: labelOfNode(chip.nodes, nodeId) || `OUT${i}`,
    })),
  }
}

const createWire = (from: PinRef, to: PinRef): Wire => ({
  id: uid('w'),
  from,
  to,
})
/* =====================================================================
 *  BUILT-IN CHIPS (Flip-Flops)
 *  -------------------------------------------------------------------
 *  Built-in blocks are packaged the same way as user chips: they are
 *  real circuits of primitive gates, flattened per-instance by the
 *  compiler. The cross-coupled feedback of the RS / D latches runs
 *  through the normal synchronous settle loop — no special-casing.
 * ===================================================================== */

const outRef = (nodeId: string, pinId: string): PinRef => ({
  nodeId,
  pinId,
  side: 'out',
})
const inRef = (nodeId: string, pinId: string): PinRef => ({
  nodeId,
  pinId,
  side: 'in',
})

/** Active-high Set/Reset latch built from two cross-coupled NOR (OR+NOT) gates. */
function buildRsLatch(): ChipDefinition {
  const R = createPrimitiveNode('INPUT', { x: 0, y: 0 }, 'R')
  const S = createPrimitiveNode('INPUT', { x: 0, y: 2 }, 'S')
  const orQ = createPrimitiveNode('OR', { x: 2, y: 0 }, 'NOR')
  const orQb = createPrimitiveNode('OR', { x: 2, y: 2 }, 'NOR')
  const qN = createPrimitiveNode('NOT', { x: 3.5, y: 0 }, '¬')
  const qN2 = createPrimitiveNode('NOT', { x: 3.5, y: 2 }, '¬')
  const Q = createPrimitiveNode('OUTPUT', { x: 5.5, y: 0 }, 'Q')
  const Qbar = createPrimitiveNode('OUTPUT', { x: 5.5, y: 2 }, 'Q̄')

  return {
    id: uid('chip'),
    name: 'RS Latch',
    color: '#22c1c3',
    builtin: true,
    inputNodeIds: [R.id, S.id],
    outputNodeIds: [Q.id, Qbar.id],
    nodes: [R, S, orQ, orQb, qN, qN2, Q, Qbar],
    wires: [
      createWire(outRef(R.id, 'out'), inRef(orQ.id, 'a')),
      createWire(outRef(qN2.id, 'out'), inRef(orQ.id, 'b')), // Q̄ feeds NOR-Q
      createWire(outRef(S.id, 'out'), inRef(orQb.id, 'a')),
      createWire(outRef(qN.id, 'out'), inRef(orQb.id, 'b')), // Q feeds NOR-Q̄
      createWire(outRef(orQ.id, 'out'), inRef(qN.id, 'in')), // Q = ¬(R + Q̄)
      createWire(outRef(orQb.id, 'out'), inRef(qN2.id, 'in')), // Q̄ = ¬(S + Q)
      createWire(outRef(qN.id, 'out'), inRef(Q.id, 'in')),
      createWire(outRef(qN2.id, 'out'), inRef(Qbar.id, 'in')),
    ],
  }
}

/** Gated D latch: samples D while EN is high, holds otherwise. It embeds an RS latch. */
function buildDLatch(rs: ChipDefinition): ChipDefinition {
  const D = createPrimitiveNode('INPUT', { x: 0, y: 0 }, 'D')
  const EN = createPrimitiveNode('INPUT', { x: 0, y: 4 }, 'EN')
  const nD = createPrimitiveNode('NOT', { x: 1.5, y: 0 }, '¬')
  const andS = createPrimitiveNode('AND', { x: 3, y: 0 }, 'D·EN')
  const andR = createPrimitiveNode('AND', { x: 3, y: 2 }, '¬D·EN')
  const latch = createChipNode(rs, { x: 5, y: 0 })
  const Q = createPrimitiveNode('OUTPUT', { x: 7.5, y: 0 }, 'Q')
  const Qbar = createPrimitiveNode('OUTPUT', { x: 7.5, y: 2 }, 'Q̄')

  return {
    id: uid('chip'),
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

/* Provide the built-in chips once, wrapped in a stable-order list. */
function makeBuiltInChips(): ChipDefinition[] {
  const rs = buildRsLatch()
  const d = buildDLatch(rs)
  return [rs, d]
}
/* =====================================================================
 *  COMPILER
 *  -------------------------------------------------------------------
 *  Custom chips are flattened into a netlist of primitive gates. Every
 *  instance gets its own prefixed copy of the internal graph, so two
 *  instances of the same chip never share latch state (isolation).
 *
 *  A "net" is the key of the terminal port that drives it: a primitive
 *  gate output or a top-level INPUT node output.
 * ===================================================================== */

interface CompiledGate {
  key: string
  type: 'AND' | 'OR' | 'NOT'
  /** Input nets; null means "floating" and reads as logic 0. */
  inputs: (string | null)[]
  /** The net this gate drives (its own output port key). */
  out: string
}

interface CompiledCircuit {
  gates: CompiledGate[]
  /** Top-level INPUT node id -> net it drives. */
  inputNets: Record<string, string>
  /** `"<topLevelNodeId>:<pinId>"` -> net (or null when unconnected). */
  pinNets: Record<string, string | null>
}

const MAX_DEPTH = 12

type CircuitData = { nodes: CircuitNode[]; wires: Wire[] }

function compileCircuit(
  circuit: CircuitData,
  chips: Record<string, ChipDefinition>,
): CompiledCircuit {
  const gates: CompiledGate[] = []
  /** input-port-key -> output-port-key (from wires) */
  const drivers = new Map<string, string>()
  /** output-port-key -> input-port-key (chip boundary crossings) */
  const aliases = new Map<string, string>()
  const inputNets: Record<string, string> = {}

  const walk = (c: CircuitData, prefix: string, depth: number) => {
    for (const wire of c.wires) {
      drivers.set(
        pinKey(prefix + wire.to.nodeId, wire.to.pinId),
        pinKey(prefix + wire.from.nodeId, wire.from.pinId),
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

  // --- resolve every input port down to a terminal net -----------------
  const memo = new Map<string, string | null>()

  const netOfInput = (inKey: string, seen: Set<string>): string | null => {
    if (seen.has(inKey)) return null // cycle safety
    seen.add(inKey)
    const driveOut = drivers.get(inKey)
    if (driveOut === undefined) return null
    const result = resolveOut(driveOut, seen)
    seen.delete(inKey)
    return result
  }

  const resolveOut = (outKey: string, seen: Set<string>): string | null => {
    if (memo.has(outKey)) return memo.get(outKey)!
    const alias = aliases.get(outKey)
    if (alias) {
      const v = resolveOut(alias, seen)
      memo.set(outKey, v)
      return v
    }
    // Reached a terminal output (gate output or top-level INPUT).
    memo.set(outKey, outKey)
    return outKey
  }

  /** Resolve the net driving a gate-input of the current circuit. */
  const resolveIn = (inKey: string): string | null => {
    if (memo.has(inKey)) return memo.get(inKey)!
    const v = netOfInput(inKey, new Set())
    memo.set(inKey, v)
    return v
  }

  // Second pass: wire up every gate input from a resolved driver.
  const gateNodeInputs = new Map<string, string[]>()
  for (const node of circuit.nodes) {
    if (node.kind !== 'AND' && node.kind !== 'OR' && node.kind !== 'NOT') continue
    gateNodeInputs.set(node.id, node.inputs.map((pin) => pinKey(node.id, pin.id)))
  }
  for (const gate of gates) {
    const keys = gateNodeInputs.get(gate.key) ?? []
    gate.inputs = keys.map((k) => resolveIn(k))
  }

  // Nets for every visible (top-level) pin, used purely for rendering.
  const pinNets: Record<string, string | null> = {}
  for (const node of circuit.nodes) {
    for (const pin of node.inputs)
      pinNets[pinKey(node.id, pin.id)] = resolveIn(pinKey(node.id, pin.id))
    for (const pin of node.outputs)
      pinNets[pinKey(node.id, pin.id)] = resolveOut(pinKey(node.id, pin.id))
  }

  return { gates, inputNets, pinNets }
}
/* =====================================================================
 *  SIMULATOR
 *  -------------------------------------------------------------------
 *  Nets are updated synchronously (all gates read the previous state,
 *  then commit together). A bounded settle loop keeps oscillators from
 *  hanging the browser while allowing feedback circuits to stabilize.
 * ===================================================================== */

const SETTLE_PASSES = 48

class Simulator {
  private state = new Map<string, boolean>()
  private compiled: CompiledCircuit = { gates: [], inputNets: {}, pinNets: {} }

  load(compiled: CompiledCircuit) {
    const next = new Map<string, boolean>()
    for (const gate of compiled.gates)
      next.set(gate.out, this.state.get(gate.out) ?? false)
    for (const net of Object.values(compiled.inputNets))
      next.set(net, this.state.get(net) ?? false)
    this.state = next
    this.compiled = compiled
  }

  reset() {
    for (const key of this.state.keys()) this.state.set(key, false)
  }

  /** Applies the user-toggled values of the top-level INPUT nodes. */
  private applyInputs(nodes: CircuitNode[]) {
    for (const node of nodes) {
      if (node.kind !== 'INPUT') continue
      const net = this.compiled.inputNets[node.id]
      if (net) this.state.set(net, !!node.value)
    }
  }

  private read(net: string | null): boolean {
    return net === null ? false : (this.state.get(net) ?? false)
  }

  /** One simulation tick: settle combinational logic, bounded by SETTLE_PASSES. */
  tick(nodes: CircuitNode[]) {
    this.applyInputs(nodes)
    const { gates } = this.compiled
    for (let pass = 0; pass < SETTLE_PASSES; pass++) {
      let changed = false
      const results: boolean[] = new Array(gates.length)
      for (let i = 0; i < gates.length; i++) {
        const g = gates[i]
        let value: boolean
        switch (g.type) {
          case 'AND':
            value = this.read(g.inputs[0]) && this.read(g.inputs[1])
            break
          case 'OR':
            value = this.read(g.inputs[0]) || this.read(g.inputs[1])
            break
          case 'NOT':
            value = !this.read(g.inputs[0])
            break
        }
        results[i] = value
      }
      for (let i = 0; i < gates.length; i++) {
        const g = gates[i]
        if (this.state.get(g.out) !== results[i]) {
          this.state.set(g.out, results[i])
          changed = true
        }
      }
      if (!changed) break
    }
  }

  /** Snapshot of pin levels for rendering: `"<nodeId>:<pinId>"` -> boolean. */
  snapshot(): SignalMap {
    const out: SignalMap = {}
    for (const [key, net] of Object.entries(this.compiled.pinNets))
      out[key] = this.read(net)
    return out
  }
}
/* =====================================================================
 *  PACKAGING (Create Chip) & HELPER COLOURS
 * ===================================================================== */

const CHIP_ACCENTS = [
  '#f59e0b',
  '#10b981',
  '#ef4444',
  '#3b82f6',
  '#ec4899',
  '#14b8a6',
  '#a78bfa',
  '#fb7185',
]
const pickAccent = () => CHIP_ACCENTS[Math.floor(Math.random() * CHIP_ACCENTS.length)]

/**
 * Builds a packaged chip definition from the currently selected nodes.
 * Internal INPUT components become left-side pins (sorted top->bottom)
 * and internal OUTPUT components become right-side pins.
 */
function packageSelectionInto(
  name: string,
  nodes: CircuitNode[],
  wires: Wire[],
  selected: Set<string>,
): ChipDefinition | null {
  const selNodes = nodes.filter((n) => selected.has(n.id))
  if (selNodes.length === 0) return null
  const selIds = new Set(selNodes.map((n) => n.id))
  const inputs = selNodes
    .filter((n) => n.kind === 'INPUT')
    .sort((a, b) => a.position.y - b.position.y)
  const outputs = selNodes
    .filter((n) => n.kind === 'OUTPUT')
    .sort((a, b) => a.position.y - b.position.y)
  if (inputs.length === 0 || outputs.length === 0) return null

  const innerWires = wires.filter(
    (w) => selIds.has(w.from.nodeId) && selIds.has(w.to.nodeId),
  )
  return {
    id: uid('chip'),
    name,
    color: pickAccent(),
    builtin: false,
    inputNodeIds: inputs.map((n) => n.id),
    outputNodeIds: outputs.map((n) => n.id),
    nodes: selNodes,
    wires: innerWires,
  }
}

/** The centroid of a group of nodes, used to place a replacement chip instance. */
function centroidOf(nodes: CircuitNode[]): Vec2 {
  if (nodes.length === 0) return { x: 0, y: 0 }
  const sum = nodes.reduce(
    (acc, n) => ({ x: acc.x + n.position.x, y: acc.y + n.position.y }),
    { x: 0, y: 0 },
  )
  return { x: Math.round(sum.x / nodes.length), y: Math.round(sum.y / nodes.length) }
}

/** Accent colours for primitive gates (vibrant, per the brief). */
const GATE_COLOURS: Record<PrimitiveType, string> = {
  AND: '#4ade80',
  OR: '#fbbf24',
  NOT: '#f472b6',
  INPUT: '#38bdf8',
  OUTPUT: '#f87171',
}

function placementLabel(p: Placement, chips: ChipDefinition[]): string {
  if (!p) return ''
  if (p.type === 'CHIP') {
    return chips.find((c) => c.id === p.chipId)?.name ?? 'Chip'
  }
  return p.kind
}

function placementColour(p: Placement, chips: ChipDefinition[]): string {
  if (!p) return '#00ffcc'
  if (p.type === 'CHIP') {
    return chips.find((c) => c.id === p.chipId)?.color ?? '#00ffcc'
  }
  return GATE_COLOURS[p.kind] ?? '#00ffcc'
}
/* =====================================================================
 *  RENDERER (Canvas 2D, 1:1 with screen space)
 * ===================================================================== */

const WIRE_HIGH = '#00ffcc' // neon cyan/green for logic 1
const WIRE_LOW = '#404040' // dark gray for logic 0
const WIRE_HOVER = '#6b7a8c'
const PIN_HIGH = '#d9fbe9'
const PIN_LOW = '#8a97a3'
const BODY = '#10151c'
const BODY_EDGE = '#d7dce2'
const LABEL = '#f2f5f8'
const GRID_DOT = 'rgba(150,165,180,0.16)'
const SEL = '#00ffcc'

const roundRect = (
  ctx: CanvasRenderingContext2D,
  x: number,
  y: number,
  w: number,
  h: number,
  r: number,
) => {
  ctx.beginPath()
  ctx.moveTo(x + r, y)
  ctx.arcTo(x + w, y, x + w, y + h, r)
  ctx.arcTo(x + w, y + h, x, y + h, r)
  ctx.arcTo(x, y + h, x, y, r)
  ctx.arcTo(x, y, x + w, y, r)
  ctx.closePath()
}

function drawGrid(ctx: CanvasRenderingContext2D, w: number, h: number) {
  ctx.fillStyle = GRID_DOT
  for (let x = GRID; x < w; x += GRID) {
    for (let y = GRID; y < h; y += GRID) {
      ctx.beginPath()
      ctx.arc(x, y, 1, 0, Math.PI * 2)
      ctx.fill()
    }
  }
}

/** Cubic bezier control points between two points (horizontal-ish wire). */
function cubic(a: Vec2, b: Vec2) {
  const mx = a.x + (b.x - a.x) / 2
  return { a, c1: { x: mx, y: a.y }, c2: { x: mx, y: b.y }, b }
}

function drawWirePath(
  ctx: CanvasRenderingContext2D,
  from: CircuitNode,
  to: CircuitNode,
  fromPin: string,
  toPin: string,
) {
  const fromIdx = from.outputs.findIndex((p) => p.id === fromPin)
  const toIdx = to.inputs.findIndex((p) => p.id === toPin)
  if (fromIdx < 0 || toIdx < 0) return
  const a = rightPinPos(from, fromIdx)
  const b = leftPinPos(to, toIdx)
  const c = cubic(a, b)
  ctx.beginPath()
  ctx.moveTo(c.a.x, c.a.y)
  ctx.bezierCurveTo(c.c1.x, c.c1.y, c.c2.x, c.c2.y, c.b.x, c.b.y)
}

/** Draw a monochrome node body. `accent` optionally tints the border. */
function drawBody(
  ctx: CanvasRenderingContext2D,
  node: CircuitNode,
  accent: string | null,
  selected: boolean,
  h: number,
) {
  const b = nodeBox(node)
  if (selected) {
    ctx.save()
    ctx.strokeStyle = SEL
    ctx.lineWidth = 2.5
    roundRect(ctx, b.x - 3, b.y - 3, b.w + 6, b.h + 6, 10)
    ctx.stroke()
    ctx.restore()
  }
  ctx.fillStyle = BODY
  roundRect(ctx, b.x, b.y, b.w, b.h, 8)
  ctx.fill()
  ctx.strokeStyle = accent ?? BODY_EDGE
  ctx.lineWidth = 1.75
  roundRect(ctx, b.x, b.y, b.w, b.h, 8)
  ctx.stroke()
  void h
}

const k = (n: string, p: string) => `${n}:${p}`

interface ChipColourMap {
  [chipId: string]: string
}

function drawNode(
  ctx: CanvasRenderingContext2D,
  node: CircuitNode,
  selected: boolean,
  signal: SignalMap,
  chipColour: ChipColourMap,
) {
  const b = nodeBox(node)

  if (node.kind === 'INPUT') {
    drawBody(ctx, node, '#38bdf8', selected, b.h)
    const value = !!node.value
    const kp = inputKnobPos(node)
    // track
    ctx.fillStyle = '#22262c'
    roundRect(ctx, node.position.x + NODE_W - SWITCH_W - 26, node.position.y + NODE_PAD, SWITCH_W, PIN_SPACING - 2, 5)
    ctx.fill()
    ctx.strokeStyle = '#3a4150'
    ctx.lineWidth = 1
    ctx.stroke()
    // knob
    const kx = value ? kp.x + 9 : kp.x - 9
    ctx.beginPath()
    ctx.arc(kx, kp.y, 7, 0, Math.PI * 2)
    ctx.fillStyle = value ? '#00ffcc' : '#8a97a3'
    ctx.fill()
    ctx.strokeStyle = '#d7dce2'
    ctx.lineWidth = 1
    ctx.stroke()
    // label
    ctx.fillStyle = LABEL
    ctx.font = '600 11px ui-sans-serif, sans-serif'
    ctx.textAlign = 'left'
    ctx.textBaseline = 'middle'
    ctx.fillText(node.label, node.position.x + 12, node.position.y + b.h / 2)
    ctx.fillStyle = value ? WIRE_HIGH : PIN_LOW
    ctx.font = '10px ui-monospace, monospace'
    ctx.textAlign = 'right'
    ctx.fillText(value ? '1' : '0', node.position.x + NODE_W - SWITCH_W - 34, node.position.y + b.h / 2)
    return
  }

  if (node.kind === 'OUTPUT') {
    drawBody(ctx, node, '#f87171', selected, b.h)
    const value = !!signal[k(node.id, node.inputs[0]?.id ?? 'in')]
    const cy = node.position.y + b.h / 2
    // LED
    if (value) {
      ctx.save()
      ctx.shadowColor = 'rgba(248,113,113,0.9)'
      ctx.shadowBlur = 18
    }
    ctx.beginPath()
    ctx.arc(node.position.x + 48, cy, 12, 0, Math.PI * 2)
    ctx.fillStyle = value ? '#f87171' : '#2a2e34'
    ctx.fill()
    ctx.strokeStyle = value ? '#fca5a5' : '#4a5160'
    ctx.lineWidth = 1.5
    ctx.stroke()
    if (value) ctx.restore()
    // label
    ctx.fillStyle = LABEL
    ctx.font = '600 11px ui-sans-serif, sans-serif'
    ctx.textAlign = 'left'
    ctx.textBaseline = 'middle'
    ctx.fillText(node.label, node.position.x + 12, cy)
    // value text
    ctx.fillStyle = value ? WIRE_HIGH : PIN_LOW
    ctx.font = '10px ui-monospace, monospace'
    ctx.textAlign = 'right'
    ctx.fillText(value ? '1' : '0', node.position.x + NODE_W - 12, cy)
    return
  }

  if (node.kind === 'CHIP') {
    const accent = node.chipId ? chipColour[node.chipId] : '#a78bfa'
    drawBody(ctx, node, accent ?? '#a78bfa', selected, b.h)
    ctx.fillStyle = LABEL
    ctx.font = '600 11px ui-sans-serif, sans-serif'
    ctx.textAlign = 'center'
    ctx.textBaseline = 'middle'
    ctx.fillText(node.label, node.position.x + b.w / 2, node.position.y + b.h / 2)
    return
  }

  // Gates: AND / OR / NOT
  const accent = GATE_COLOURS[node.kind] ?? '#e6e9ee'
  drawBody(ctx, node, accent, selected, b.h)
  const cx = node.position.x + b.w / 2
  const cy = node.position.y + b.h / 2
  const glyph =
    node.kind === 'AND' ? '∧' : node.kind === 'OR' ? '∨' : '¬'
  ctx.fillStyle = accent
  ctx.font = '800 30px ui-sans-serif, sans-serif'
  ctx.textAlign = 'center'
  ctx.textBaseline = 'middle'
  ctx.fillText(glyph, cx, cy + 1)
  // label above
  ctx.fillStyle = LABEL
  ctx.font = '600 11px ui-sans-serif, sans-serif'
  ctx.fillText(node.label === '¬' ? 'NOT' : node.label, cx, node.position.y + 12)
}
function drawPin(
  ctx: CanvasRenderingContext2D,
  x: number,
  y: number,
  high: boolean,
) {
  ctx.beginPath()
  ctx.arc(x, y, PIN_R, 0, Math.PI * 2)
  ctx.fillStyle = high ? WIRE_HIGH : PIN_LOW
  ctx.fill()
  ctx.strokeStyle = high ? WIRE_HIGH : PIN_HIGH
  ctx.lineWidth = 1
  ctx.stroke()
}

interface WireView {
  wire: Wire
  from: CircuitNode
  to: CircuitNode
  path: { a: Vec2; c1: Vec2; c2: Vec2; b: Vec2 }
}

/** Compute a wire's endpoints/cubic and whether the path is on screen. */
function wireView(from: CircuitNode, to: CircuitNode, wire: Wire): WireView | null {
  const fromIdx = from.outputs.findIndex((p) => p.id === wire.from.pinId)
  const toIdx = to.inputs.findIndex((p) => p.id === wire.to.pinId)
  if (fromIdx < 0 || toIdx < 0) return null
  const a = rightPinPos(from, fromIdx)
  const b = leftPinPos(to, toIdx)
  return { wire, from, to, path: cubic(a, b) }
}

function drawScene(
  ctx: CanvasRenderingContext2D,
  w: number,
  h: number,
  nodes: CircuitNode[],
  wires: Wire[],
  signal: SignalMap,
  selected: Set<string>,
  hoverWireId: string | null,
  chipColour: ChipColourMap,
  pending: { start: PinRef; startPos: Vec2; end: Vec2 } | null,
  box: { x: number; y: number; w: number; h: number } | null,
  placing: { x: number; y: number; label: string; colour: string } | null,
  activeWireId: string | null,
) {
  ctx.clearRect(0, 0, w, h)
  // background fill (monochrome, near-black)
  ctx.fillStyle = '#0f0f0f'
  ctx.fillRect(0, 0, w, h)
  drawGrid(ctx, w, h)

  const byId = new Map(nodes.map((n) => [n.id, n]))

  // A wire is "active" when its driving node/output pin is high.
  const wireActive = (wire: Wire): boolean => {
    if (!byId.has(wire.from.nodeId)) return false
    return !!signal[k(wire.from.nodeId, wire.from.pinId)]
  }

  // --- wires ---
  for (const wire of wires) {
    const from = byId.get(wire.from.nodeId)
    const to = byId.get(wire.to.nodeId)
    if (!from || !to) continue
    const vw = wireView(from, to, wire)
    if (!vw) continue
    const high = wireActive(wire)
    const isHover = hoverWireId === wire.id
    const isActiveWire = activeWireId === wire.id
    const p = vw.path
    // glow pass for high wires
    if (high) {
      ctx.save()
      ctx.strokeStyle = 'rgba(0,255,204,0.16)'
      ctx.lineWidth = 7
      ctx.beginPath()
      ctx.moveTo(p.a.x, p.a.y)
      ctx.bezierCurveTo(p.c1.x, p.c1.y, p.c2.x, p.c2.y, p.b.x, p.b.y)
      ctx.stroke()
      ctx.restore()
    }
    ctx.strokeStyle = isHover ? WIRE_HOVER : high ? WIRE_HIGH : WIRE_LOW
    ctx.lineWidth = isActiveWire ? 3 : 2
    if (isHover) ctx.setLineDash([6, 4])
    ctx.beginPath()
    ctx.moveTo(p.a.x, p.a.y)
    ctx.bezierCurveTo(p.c1.x, p.c1.y, p.c2.x, p.c2.y, p.b.x, p.b.y)
    ctx.stroke()
    ctx.setLineDash([])
  }

  // --- nodes ---
  for (const node of nodes) {
    drawNode(ctx, node, selected.has(node.id), signal, chipColour)
  }

  // --- pins (drawn on top so they read as connection points) ---
  for (const node of nodes) {
    for (const pin of enumeratePins(node)) {
      const high = !!signal[k(pin.nodeId, pin.pinId)]
      drawPin(ctx, pin.pos.x, pin.pos.y, high)
    }
  }

  // --- pending wire while dragging ---
  if (pending) {
    const tx = pending.end.x
    const ty = pending.end.y
    ctx.strokeStyle = WIRE_HIGH
    ctx.setLineDash([6, 5])
    ctx.lineWidth = 2
    const p = cubic(pending.startPos, { x: tx, y: ty })
    ctx.beginPath()
    ctx.moveTo(p.a.x, p.a.y)
    ctx.bezierCurveTo(p.c1.x, p.c1.y, p.c2.x, p.c2.y, p.b.x, p.b.y)
    ctx.stroke()
    ctx.setLineDash([])
    // small dot at the dragged end
    ctx.beginPath()
    ctx.arc(tx, ty, 4, 0, Math.PI * 2)
    ctx.fillStyle = WIRE_HIGH
    ctx.fill()
  }

  // --- placing ghost ---
  if (placing) {
    ctx.globalAlpha = 0.75
    ctx.fillStyle = 'rgba(0,255,204,0.08)'
    ctx.strokeStyle = placing.colour
    ctx.lineWidth = 1.5
    roundRect(ctx, placing.x, placing.y, NODE_W, 64, 8)
    ctx.fill()
    ctx.stroke()
    ctx.fillStyle = LABEL
    ctx.font = '600 12px ui-sans-serif, sans-serif'
    ctx.textAlign = 'center'
    ctx.textBaseline = 'middle'
    ctx.fillText(placing.label, placing.x + NODE_W / 2, placing.y + 32)
    ctx.globalAlpha = 1
  }

  // --- marquee box ---
  if (box && (Math.abs(box.w) > 1 || Math.abs(box.h) > 1)) {
    const rx = Math.min(box.x, box.x + box.w)
    const ry = Math.min(box.y, box.y + box.h)
    const rw = Math.abs(box.w)
    const rh = Math.abs(box.h)
    ctx.fillStyle = 'rgba(0,255,204,0.08)'
    ctx.strokeStyle = 'rgba(0,255,204,0.65)'
    ctx.lineWidth = 1
    ctx.beginPath()
    ctx.rect(rx, ry, rw, rh)
    ctx.fill()
    ctx.stroke()
  }
}
/* =====================================================================
 *  MAIN COMPONENT
 * ===================================================================== */

type DragMode =
  | { kind: 'move'; ids: string[]; startWorld: Vec2; origin: Map<string, Vec2> }
  | { kind: 'box'; startX: number; startY: number; endX: number; endY: number }
  | { kind: 'wire'; start: PinRef; startPos: Vec2; end: Vec2 }
  | null

const SIM_TPS = 60

export default function LogicSimulator() {
  const [nodes, setNodes] = useState<CircuitNode[]>([])
  const [wires, setWires] = useState<Wire[]>([])
  const [chips, setChips] = useState<ChipDefinition[]>(() => makeBuiltInChips())
  const [selected, setSelected] = useState<Set<string>>(new Set())
  const [tool, setTool] = useState<Tool>('select')
  const [placement, setPlacement] = useState<Placement>(null)
  const [play, setPlay] = useState(false)
  const [, setFrameTick] = useState(0)

  const canvasRef = useRef<HTMLCanvasElement>(null)
  const drag = useRef<DragMode>(null)
  const pending = useRef<{ start: PinRef; startPos: Vec2 } | null>(null)
  const hoverWire = useRef<string | null>(null)
  const signal = useRef<SignalMap>({})
  const mousePos = useRef<Vec2>({ x: 0, y: 0 })

  // Mutable mirrors kept in sync with canonical React state so that the
  // rAF render loop and native event handlers never go stale. Reading from
  // refs during render is avoided; they are updated after commit.
  const live = useRef({ nodes, wires, chips, selected, placement, tool })
  useEffect(() => {
    live.current = { nodes, wires, chips, selected, placement, tool }
  })

  const simulator = useMemo(() => new Simulator(), [])

  const chipsById = useMemo(
    () => Object.fromEntries(chips.map((c) => [c.id, c])),
    [chips],
  )
  const compiled = useMemo(
    () => compileCircuit({ nodes, wires }, chipsById),
    [nodes, wires, chipsById],
  )
  simulator.load(compiled)
// ---- simulation loop (independent of the render loop) -----------------
  useEffect(() => {
    if (!play) return
    const id = setInterval(() => {
      const s = live.current
      simulator.tick(s.nodes)
      signal.current = simulator.snapshot()
      // There is no React state depending on pin levels; the rAF loop reads
      // `signal.current` directly. We only bump a frame tick so the canvas
      // loop knows to redraw after a pause-restart.
      setFrameTick((t) => t + 1)
    }, 1000 / SIM_TPS)
    return () => clearInterval(id)
  }, [play, simulator])

  const togglePlay = () => {
    setPlay((p) => {
      if (!p) {
        simulator.tick(live.current.nodes)
        signal.current = simulator.snapshot()
      }
      return !p
    })
  }

  // ---- helpers ---------------------------------------------------------
  const posFromEvent = (e: React.PointerEvent) => {
    const rect = canvasRef.current!.getBoundingClientRect()
    return { x: e.clientX - rect.left, y: e.clientY - rect.top }
  }

  const findPinAt = (p: Vec2): EnumeratedPin | null => {
    let best: EnumeratedPin | null = null
    let bestD = Infinity
    for (const node of live.current.nodes) {
      for (const pin of enumeratePins(node)) {
        const d = Math.hypot(p.x - pin.pos.x, p.y - pin.pos.y)
        if (d < PIN_R + 5 && d < bestD) {
          bestD = d
          best = pin
        }
      }
    }
    return best
  }

  const findNodeAt = (p: Vec2): CircuitNode | null => {
    for (let i = live.current.nodes.length - 1; i >= 0; i--) {
      const n = live.current.nodes[i]
      if (hitNode(n, p)) return n
    }
    return null
  }

  const findHoveredWire = (p: Vec2): string | null => {
    const nodesById = new Map(live.current.nodes.map((n) => [n.id, n]))
    let bestId: string | null = null
    let bestD = 14
    for (const wire of live.current.wires) {
      const from = nodesById.get(wire.from.nodeId)
      const to = nodesById.get(wire.to.nodeId)
      if (!from || !to) continue
      const vw = wireView(from, to, wire)
      if (!vw) continue
      const pa = vw.path.a
      const mid = { x: pa.x + (vw.path.b.x - pa.x) / 2, y: pa.y }
      const d = Math.min(
        distToSegment(p, pa, mid),
        distToSegment(p, mid, vw.path.b),
      )
      if (d < bestD) {
        bestD = d
        bestId = wire.id
      }
    }
    return bestId
  }

  /** Place a node from the current placement mode at screen position p. */
  const place = (p: Vec2) => {
    if (!placement) return
    const snapped: Vec2 = { x: snap(p.x), y: snap(p.y) }
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
// ---- pointer interaction ---------------------------------------------
  const onPointerDown = (e: React.PointerEvent) => {
    const p = posFromEvent(e)
    canvasRef.current!.setPointerCapture(e.pointerId)

    // 1) If a placement is armed, place a component and stop.
    if (placement) {
      place(p)
      return
    }

    const pin = findPinAt(p)

    // 2) Starting / completing a wire. Wires always connect output->input.
    if (tool === 'wire' && pin) {
      if (pin.side === 'out') {
        drag.current = {
          kind: 'wire',
          start: { nodeId: pin.nodeId, pinId: pin.pinId, side: 'out' },
          startPos: pin.pos,
          end: pin.pos,
        }
      } else if (pin.side === 'in' && pending.current) {
        finishWire(pending.current.start, {
          nodeId: pin.nodeId,
          pinId: pin.pinId,
          side: 'in',
        })
        pending.current = null
      }
      return
    }

    // 3) In select mode, dragging OFF an output pin starts a wire; dragging
    //    a node body moves it; an input pin closes a pending wire.
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
        // Pressing an INPUT node's toggle-switch flips its value instead of
        // moving the node.
        if (node.kind === 'INPUT') {
          const kp = inputKnobPos(node)
          if (
            p.x >= node.position.x + NODE_W - SWITCH_W - 26 &&
            p.x <= node.position.x + NODE_W - 20 &&
            Math.abs(p.y - kp.y) <= PIN_SPACING / 2
          ) {
            toggleInputValue(node.id)
            setSelected(new Set([node.id]))
            return
          }
        }
        const multi = e.shiftKey || selected.has(node.id)
        const nextSel = new Set<string>(multi ? selected : [])
        nextSel.add(node.id)
        setSelected(nextSel)
        const ids = Array.from(nextSel)
        const origin = new Map<string, Vec2>()
        for (const n of live.current.nodes) if (nextSel.has(n.id)) origin.set(n.id, { ...n.position })
        drag.current = { kind: 'move', ids, startWorld: p, origin }
        return
      }

      // Empty space: start a marquee box selection.
      setSelected(new Set())
      drag.current = { kind: 'box', startX: p.x, startY: p.y, endX: p.x, endY: p.y }
    }
  }

  const onPointerMove = (e: React.PointerEvent) => {
    const p = posFromEvent(e)
    mousePos.current = p

    if (drag.current && drag.current.kind === 'box') {
      drag.current.endX = p.x
      drag.current.endY = p.y
    } else if (drag.current && drag.current.kind === 'wire') {
      drag.current.end = p
    } else if (drag.current && drag.current.kind === 'move') {
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
    const p = posFromEvent(e)
    const d = drag.current
    if (d && d.kind === 'box') {
      const minX = Math.min(d.startX, d.endX)
      const maxX = Math.max(d.startX, d.endX)
      const minY = Math.min(d.startY, d.endY)
      const maxY = Math.max(d.startY, d.endY)
      const nextSel = new Set<string>()
      for (const n of live.current.nodes) {
        const b = nodeBox(n)
        if (
          b.x < maxX && b.x + b.w > minX &&
          b.y < maxY && b.y + b.h > minY
        ) {
          nextSel.add(n.id)
        }
      }
      setSelected(nextSel)
    } else if (d && d.kind === 'wire') {
      const pin = findPinAt(p)
      if (pin && pin.side === 'in') {
        finishWire(d.start, { nodeId: pin.nodeId, pinId: pin.pinId, side: 'in' })
        pending.current = null
      } else {
        pending.current = { start: d.start, startPos: d.startPos }
      }
    }
    drag.current = null
  }
/** Registers a wire, replacing any existing wire driving the same input. */
  const finishWire = (from: PinRef, to: PinRef) => {
    if (isPinRefEqual(from, to)) return
    if (from.nodeId === to.nodeId) return // no self-loops
    setWires((ws) => {
      const filtered = ws.filter((w) => !isPinRefEqual(w.to, to))
      return [...filtered, createWire(from, to)]
    })
  }

  const deleteSelection = () => {
    const ids = new Set(selected)
    setNodes((ns) => ns.filter((n) => !ids.has(n.id)))
    setWires((ws) =>
      ws.filter((w) => !ids.has(w.from.nodeId) && !ids.has(w.to.nodeId)),
    )
    setSelected(new Set())
  }

  const toggleInputValue = (id: string) => {
    setNodes((ns) =>
      ns.map((n) =>
        n.id === id && n.kind === 'INPUT' ? { ...n, value: !n.value } : n,
      ),
    )
  }

  /**
   * Packages the current selection into a reusable chip. Returns true on
   * success. The sub-circuit is replaced on the canvas by one instance.
   */
  const createChip = (name: string): boolean => {
    const def = packageSelectionInto(
      name,
      live.current.nodes,
      live.current.wires,
      live.current.selected,
    )
    if (!def) return false
    setChips((cs) => [...cs, def])
    const ids = new Set(def.nodes.map((n) => n.id))
    const centroid = centroidOf(def.nodes)
    const instance = createChipNode(def, centroid)
    setNodes((ns) => [...ns.filter((n) => !ids.has(n.id)), instance])
    setWires((ws) =>
      ws.filter((w) => !ids.has(w.from.nodeId) && !ids.has(w.to.nodeId)),
    )
    setSelected(new Set([instance.id]))
    return true
  }

  const handleCreateChipClick = () => {
    if (live.current.selected.size === 0) return
    const name = window.prompt('Name your custom chip:', 'My Chip')
    if (name && name.trim()) createChip(name.trim())
  }

  const onContextMenu = (e: React.PointerEvent<HTMLCanvasElement>) => {
    e.preventDefault()
    const p = posFromEvent(e)
    const hw = findHoveredWire(p)
    if (hw) {
      setWires((ws) => ws.filter((w) => w.id !== hw))
    } else if (selected.size > 0) {
      deleteSelection()
    }
  }

  const clearAll = () => {
    setNodes([])
    setWires([])
    setSelected(new Set())
    setPlacement(null)
    pending.current = null
    setPlay(false)
    simulator.reset()
    signal.current = {}
  }

  // ---- keyboard shortcuts ----------------------------------------------
  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      if (e.key === 'Escape') {
        pending.current = null
        setPlacement(null)
      }
      if ((e.key === 'Delete' || e.key === 'Backspace') && selected.size > 0) {
        e.preventDefault()
        deleteSelection()
      }
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [selected])
// ---- canvas render loop (reads refs; 1:1 coordinate system) -----------
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
      if (canvas.width !== Math.round(cw * dpr) || canvas.height !== Math.round(ch * dpr)) {
        canvas.width = Math.round(cw * dpr)
        canvas.height = Math.round(ch * dpr)
      }
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0)

      const s = live.current
      const box = drag.current && drag.current.kind === 'box'
        ? {
            x: drag.current.startX,
            y: drag.current.startY,
            w: drag.current.endX - drag.current.startX,
            h: drag.current.endY - drag.current.startY,
          }
        : null

      // A draggable wire while actively dragging off an output pin, OR a
      // committed pending wire shown after the pointer is released.
      let pnd:
        | { start: PinRef; startPos: Vec2; end: Vec2 }
        | null = null
      if (drag.current && drag.current.kind === 'wire') {
        pnd = {
          start: drag.current.start,
          startPos: drag.current.startPos,
          end: drag.current.end,
        }
      } else if (pending.current) {
        pnd = {
          start: pending.current.start,
          startPos: pending.current.startPos,
          end: pending.current.startPos,
        }
      }

      const chipColour: ChipColourMap = {}
      for (const c of s.chips) chipColour[c.id] = c.color

      // Ghost preview while a placement is armed; anchored at the cursor.
      const curPlacement = s.placement
      const placing = curPlacement && mousePos.current
        ? {
            x: snap(mousePos.current.x - NODE_W / 2),
            y: snap(mousePos.current.y - 20),
            label: placementLabel(curPlacement, s.chips),
            colour: placementColour(curPlacement, s.chips),
          }
        : null

      drawScene(
        ctx,
        cw,
        ch,
        s.nodes,
        s.wires,
        signal.current,
        s.selected,
        hoverWire.current,
        chipColour,
        pnd,
        box,
        placing,
        null,
      )
    }
    loop()
    return () => cancelAnimationFrame(raf)
  }, [])
// ---- top-level rendering ----------------------------------------------
  const paletteBtn =
    'inline-flex flex-col items-center gap-1 rounded-md px-3 py-1.5 text-xs font-medium transition select-none'
  const paletteActive =
    'bg-[#00ffcc]/15 text-[#7dffdf] ring-1 ring-[#00ffcc]/50'
  const paletteIdle = 'text-slate-300 hover:bg-white/5 hover:text-white'

  const isPrimActive = (k: PrimitiveType) =>
    placement?.type === 'PRIMITIVE' && placement.kind === k
  const isChipActive = (id: string) =>
    placement?.type === 'CHIP' && placement.chipId === id

  const chipName = (chip: ChipDefinition) =>
    chip.name.slice(0, 2).toUpperCase()

  return (
    <div className="flex h-screen w-screen flex-col overflow-hidden bg-[#0b0f16] text-slate-100">
      {/* ---------------- Top bar ---------------- */}
      <header className="flex h-12 shrink-0 items-center gap-2 border-b border-white/10 bg-[#0d1219]/90 px-3">
        <div className="mr-2 flex items-center gap-2">
          <span className="grid h-7 w-7 place-items-center rounded bg-[#0f0f0f] text-sm text-[#00ffcc] ring-1 ring-white/20">
            ⊼
          </span>
          <span className="text-sm font-bold tracking-tight text-slate-100">
            logic<span className="text-[#00ffcc]">craft</span>
          </span>
        </div>

        <div className="flex items-center gap-0.5 rounded-md bg-white/5 p-0.5 ring-1 ring-white/10">
          {(['select', 'wire'] as Tool[]).map((t) => (
            <button
              key={t}
              onClick={() => setTool(t)}
              title={t === 'select' ? 'Select · drag to marquee' : 'Wire output → input'}
              className={`${paletteBtn} px-2.5 ${tool === t ? paletteActive : paletteIdle}`}
            >
              {t === 'select' ? '◆ Select' : '⌁ Wire'}
            </button>
          ))}
        </div>

        <div className="mx-1 h-6 w-px bg-white/10" />

        <button
          onClick={handleCreateChipClick}
          disabled={selected.size === 0}
          title="Package the selection into a reusable chip (needs Input + Output)"
          className={`${paletteBtn} ${
            selected.size === 0
              ? 'cursor-not-allowed text-slate-600'
              : 'bg-emerald-500/15 text-emerald-300 hover:bg-emerald-500/25'
          }`}
        >
          <span className="text-base leading-none">⬒</span>
          <span className="hidden sm:inline">Create Chip</span>
        </button>

        <div className="flex-1" />

        <div className="hidden items-center gap-2 text-[11px] text-slate-500 md:flex">
          {nodes.length} nodes · {wires.length} wires · {selected.size} selected
        </div>

        <button
          onClick={togglePlay}
          title={play ? 'Pause simulation' : 'Run simulation'}
          className={`${paletteBtn} ${
            play
              ? 'bg-amber-500/20 text-amber-300 ring-1 ring-amber-500/40'
              : 'bg-emerald-500/15 text-emerald-300 hover:bg-emerald-500/25'
          }`}
        >
          <span className="text-base leading-none">{play ? '⏸' : '▶'}</span>
          <span className="hidden sm:inline">{play ? 'Pause' : 'Run'}</span>
        </button>

        <button
          onClick={clearAll}
          title="Clear all"
          className={`${paletteBtn} text-slate-400 hover:bg-red-500/20 hover:text-red-300`}
        >
          <span className="text-base leading-none">⌫</span>
        </button>
      </header>

      {/* ---------------- Canvas ---------------- */}
      <main className="relative min-h-0 flex-1">
        <canvas
          ref={canvasRef}
          className="h-full w-full touch-none select-none"
          onPointerDown={onPointerDown}
          onPointerMove={onPointerMove}
          onPointerUp={onPointerUp}
          onPointerCancel={onPointerUp}
          onContextMenu={onContextMenu}
        />

        <div className="pointer-events-none absolute bottom-3 left-1/2 z-10 -translate-x-1/2 whitespace-nowrap rounded-md bg-black/50 px-3 py-1 text-xs text-slate-400 ring-1 ring-white/10">
          {placement
            ? `Click to place ${placementLabel(placement, chips)} · Esc to cancel`
            : pending.current
              ? 'Click an input pin to complete the wire'
              : 'Drag from an output pin to wire · drag bodies to move · drag empty space to box-select · right-click a wire to delete'}
        </div>
      </main>
{/* ---------------- Bottom palette ---------------- */}
      <footer className="z-20 flex shrink-0 items-stretch gap-3 overflow-x-auto border-t border-white/10 bg-[#0d1219]/95 px-3 py-2">
        {/* Input / Output */}
        <section className="flex flex-col">
          <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider text-slate-500">
            I/O
          </h3>
          <div className="flex flex-1 items-center gap-1.5">
            {(['INPUT', 'OUTPUT'] as PrimitiveType[]).map((k) => (
              <button
                key={k}
                onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
                className={`${paletteBtn} ${isPrimActive(k) ? paletteActive : paletteIdle}`}
              >
                <span
                  className="grid h-8 w-8 place-items-center rounded bg-[#0f0f0f] font-mono text-sm font-bold ring-1"
                  style={{ color: GATE_COLOURS[k], borderColor: `${GATE_COLOURS[k]}66` }}
                >
                  {k === 'INPUT' ? 'I' : 'O'}
                </span>
                <span>{k === 'INPUT' ? 'Toggle' : 'Output'}</span>
              </button>
            ))}
          </div>
        </section>

        <div className="my-1 w-px bg-white/10" />

        {/* Gates */}
        <section className="flex flex-col">
          <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider text-slate-500">
            Gates
          </h3>
          <div className="flex flex-1 items-center gap-1.5">
            {(['AND', 'OR', 'NOT'] as PrimitiveType[]).map((k) => (
              <button
                key={k}
                onClick={() => setPlacement({ type: 'PRIMITIVE', kind: k })}
                className={`${paletteBtn} ${isPrimActive(k) ? paletteActive : paletteIdle}`}
              >
                <span
                  className="grid h-8 w-8 place-items-center rounded bg-[#0f0f0f] font-mono text-base font-bold ring-1"
                  style={{ color: GATE_COLOURS[k], borderColor: `${GATE_COLOURS[k]}66` }}
                >
                  {k === 'AND' ? '∧' : k === 'OR' ? '∨' : '¬'}
                </span>
                <span>{k}</span>
              </button>
            ))}
          </div>
        </section>

        <div className="my-1 w-px bg-white/10" />

        {/* Flip-Flops + Custom Chips */}
        <section className="flex min-w-0 flex-col">
          <h3 className="mb-1 text-[10px] font-semibold uppercase tracking-wider text-slate-500">
            Blocks
          </h3>
          <div className="flex flex-1 items-center gap-1.5 overflow-x-auto">
            {chips.map((chip) => (
              <button
                key={chip.id}
                onClick={() => setPlacement({ type: 'CHIP', chipId: chip.id })}
                title={`${chip.inputNodeIds.length} in · ${chip.outputNodeIds.length} out · ${chip.builtin ? 'built-in' : 'custom'}`}
                className={`${paletteBtn} ${isChipActive(chip.id) ? paletteActive : paletteIdle}`}
              >
                <span
                  className="grid h-8 min-w-8 place-items-center rounded bg-[#0f0f0f] px-1 font-mono text-sm font-bold ring-1"
                  style={{ color: chip.color, borderColor: `${chip.color}66` }}
                >
                  {chipName(chip)}
                </span>
                <span className="max-w-24 truncate">{chip.name}</span>
              </button>
            ))}
            {!chips.length && (
              <span className="px-1 text-[11px] text-slate-600">
                Select nodes + press Create Chip to add custom blocks
              </span>
            )}
          </div>
        </section>
      </footer>
    </div>
  )
}