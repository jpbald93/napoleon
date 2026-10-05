# napoleon — Napoleon's theorem (complex coordinates) — DONE

Project jack:~/napoleon, Lean v4.33.1, lib `Napoleon` (one file `Napoleon/Basic.lean`, ~130 lines). Not pushed.

## Prior art
- Mathlib: not present (not in 100.yaml/1000.yaml formalised list; checked by requester).
- **Lean 4 (third party, already exists):** https://github.com/imran-tanrikolu/Napoleon-s-Theorem-in-Lean4 (`napoleantheorem.lean`, 64 lines, no sorry; complex coordinates, `IsEquilateral z1 z2 z3 := Σ(zi-zj)^2 = 0`, i.e. the algebraic criterion, not distances). Also listed on ProofAtlas ("Napoleon theorem algebraic core"). Our version states equality of *distances* and proves the erected triangles are equilateral and outward — so it is a cleaner/fuller statement but not novel.
- Isabelle AFP: "Napoleon's Theorem" by Arthur Freitas Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz (https://www.isa-afp.org/, entry list).
- Coq: Narboux et al. / "Proofs with Coq of theorems in plane geometry using oriented angles" (https://inria.hal.science/inria-00072226v1) mentions Napoleon.
- The task said proceed; since this is a short self-contained coordinate proof, I completed it rather than STOP-PRIOR-ART. Treat as prior-art-exists.

## Model
Plane = ℂ. `ωo = 1/2 - (√3/2)i` (rotation by -π/3), `ωi` its conjugate. `apex ω P Q = P + ω(Q-P)`; `centroid P Q R = (P+Q+R)/3`;
`Ga ω A B C = centroid B C (apex ω B C)`, `Gb … = centroid C A (apex ω C A)`, `Gc … = centroid A B (apex ω A B)`.
`signedArea P Q R = Im(conj(Q-P)(R-P))/2`.

## Headline statements (Napoleon/Basic.lean)
- L64 `theorem apex_equilateral {ω : ℂ} (h1 : ‖ω‖ = 1) (h2 : ‖1 - ω‖ = 1) (P Q : ℂ) : dist P Q = dist P (apex ω P Q) ∧ dist P Q = dist Q (apex ω P Q)`
- L81 `theorem napoleon_general {ω : ℂ} (h : ω ^ 2 - ω + 1 = 0) (h1 : ‖ω‖ = 1) (h2 : ‖1 - ω‖ = 1) (A B C : ℂ) : dist (Ga ω A B C) (Gb ω A B C) = dist (Gb ω A B C) (Gc ω A B C) ∧ dist (Gb ω A B C) (Gc ω A B C) = dist (Gc ω A B C) (Ga ω A B C)`
- L98 `theorem napoleon_outer (A B C : ℂ) : dist (Ga ωo A B C) (Gb ωo A B C) = dist (Gb ωo A B C) (Gc ωo A B C) ∧ dist (Gb ωo A B C) (Gc ωo A B C) = dist (Gc ωo A B C) (Ga ωo A B C)`
- L104 `theorem napoleon_inner` — same with `ωi` (inner Napoleon triangle).
- L112 `theorem apex_outward (P Q : ℂ) : signedArea P Q (apex ωo P Q) = -(Real.sqrt 3 / 4) * normSq (Q - P)` — each erected triangle is clockwise, so for a counter-clockwise ABC (`0 < signedArea A B C`) it lies on the far side of its base: outward.
- L119 non-vacuity `example`: A=0,B=1,C=i: `0 < signedArea 0 1 I`, the Napoleon equality, and `dist Ga Gb ≠ 0` (numerically 1.115…).
Key lemma L74: `Gb - Ga = ω (Gc - Ga)` by `linear_combination ((A-2B+C)/3) * h`.

## Hypotheses
No non-degeneracy hypothesis is needed: the identity holds for all A,B,C (degenerate/collinear triangles give a valid, possibly point, equilateral triangle). Non-degeneracy + orientation (`0 < signedArea A B C`) only matter to *interpret* ωo as "outward" (`apex_outward`); for clockwise ABC the ωo triangles are inward and `napoleon_inner` covers the other choice, so both consistent orientations are proved. In `napoleon_general`, `h` (ω primitive 6th root of unity) drives the identity and `h1,h2` turn it into distances. Mixed orientations are false (numeric negative control).

## Numeric check (code/check_napoleon.py)
1000 random triangles: max spread of the 3 distances 3.6e-15 (outward), 2.7e-15 (inward). Negative controls: 50° rotation min spread 0.0226; mixed orientations spread 1.15.

## Gate (seen)
- `lake build`: `Build completed successfully (8708 jobs).` EXIT 0, 0 warnings.
- forbidden grep on `Napoleon Napoleon.lean`: empty.
- scratch/ax.out: napoleon_outer, napoleon_inner, napoleon_general, apex_equilateral, apex_outward → `[propext, Classical.choice, Quot.sound]`.

## Not done
No EuclideanSpace ℝ (Fin 2) / `EuclideanGeometry` version; "outward" stated via signed area rather than half-planes; Napoleon point concurrence / area formula not formalised.
