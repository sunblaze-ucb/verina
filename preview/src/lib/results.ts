// pass@1 values from the ICLR 2026 camera-ready paper.
// CodeGen overall / VERINA-A / VERINA-B = Tables 8 / 9 / 10.
// SpecGen S&C and ProofGen = Figure 5.
// Code&Spec, End-to-End = Figure 6.

export interface ModelResult {
  name: string
  short?: string
  code: number       // CodeGen pass@1 %
  spec: number       // SpecGen Sound & Complete pass@1 %
  proof: number      // ProofGen pass@1 %
  codeA: number      // CodeGen on VERINA-A
  codeB: number      // CodeGen on VERINA-B
  codeSpec?: number  // Code & Spec score
  e2e?: number       // End-to-End score
}

export const MODELS: ModelResult[] = [
  { name: 'GPT 4o-mini',           code: 28.6, spec: 22.4, proof: 0.6, codeA: 44.0, codeB:  8.4, codeSpec: 15.5, e2e: 0.5 },
  { name: 'GPT 4o',                code: 45.7, spec: 36.5, proof: 3.6, codeA: 61.7, codeB: 24.7, codeSpec: 32.6, e2e: 3.2 },
  { name: 'GPT 4.1',               code: 56.4, spec: 45.0, proof: 0.0, codeA: 69.8, codeB: 38.8, codeSpec:  9.1, e2e: 0.0 },
  { name: 'o4-mini',               code: 61.4, spec: 42.6, proof: 2.7, codeA: 68.7, codeB: 51.9, codeSpec: 29.4, e2e: 2.7 },
  { name: 'o3',                    code: 72.6, spec: 52.3, proof: 4.9, codeA: 75.9, codeB: 68.4, codeSpec: 33.7, e2e: 0.0 },
  { name: 'Claude Sonnet 3.7',     code: 44.2, spec: 45.6, proof: 1.2, codeA: 54.0, codeB: 31.4, codeSpec: 29.9, e2e: 1.1 },
  { name: 'Claude Opus 4.0',       code: 66.7, spec: 47.6, proof: 2.4, codeA: 78.5, codeB: 51.4, codeSpec: 41.2, e2e: 3.2 },
  { name: 'Gemini 2.5 Flash',      code: 36.5, spec: 45.0, proof: 1.9, codeA: 50.2, codeB: 18.5, codeSpec: 26.7, e2e: 2.1 },
  { name: 'DeepSeek V3',           code: 36.0, spec: 34.7, proof: 0.7, codeA: 49.8, codeB: 18.0, codeSpec: 23.0, e2e: 1.6 },
  { name: 'Qwen 3 235B-A22B-FP8', short: 'Qwen 3 235B', code: 20.0, spec: 15.9, proof: 0.0, codeA: 32.8, codeB: 3.2, codeSpec: 18.7, e2e: 0.5 },
]
