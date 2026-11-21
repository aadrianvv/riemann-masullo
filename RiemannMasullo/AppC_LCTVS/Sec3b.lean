module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral kernels

Masullo, Appendix C, §C.3.7, pp. 707–708.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace RiemannMasullo

variable {X : Type*}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]

-- TODO(paper-gap): The diagonal need not be product-null as asserted on p. 707.
-- For a one-point space with unit point mass, the diagonal has product measure one.

/-- Paper: (C.3.7.1), p. 708. A square-integrable kernel defines a Hilbert-Schmidt
endomorphism of L².
Deviation: The kernel is an L² class. The correspondence from (C.3.6.5)–(C.3.6.6)
uses source-first coordinates, so the operator is obtained by swapping the coordinates. -/
def integralKernelOperator (k : Lp ℂ 2 (μ.prod μ)) :
    hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 μ) :=
  (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose
    (Lp.compMeasurePreserving Prod.swap (Measure.measurePreserving_swap (μ := μ) (ν := μ)) k)

/-- Paper: (C.3.7.1), p. 708. The operator acts by integrating the product of the
kernel and the input function in the source variable.
Deviation: The integral is required to be defined and to give the operator value
almost everywhere in the target variable. -/
theorem integralKernelOperator_apply (k : Lp ℂ 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
      (integralKernelOperator μ k).val f x = ∫ y, k (x, y) * f y ∂μ := by
  let hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  let swapped := Lp.compMeasurePreserving Prod.swap hswap k
  have hkernel : ∀ᵐ p ∂(μ.prod μ), swapped p.swap = k p :=
    hswap.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving k hswap)
  filter_upwards [Measure.ae_ae_of_ae_prod hkernel,
    (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose_spec.2 swapped f] with x hx happly
  have hmul : (fun y ↦ swapped (y, x) * f y) =ᵐ[μ] fun y ↦ k (x, y) * f y := by
    filter_upwards [hx] with y hy
    exact congrArg (· * f y) hy
  exact ⟨happly.1.congr hmul, happly.2.trans (integral_congr_ae hmul)⟩

/-- Paper: Theorem C.3.7.1(1), p. 708. The Hilbert-Schmidt norm of the integral
operator is the L² norm of the kernel. -/
theorem schattenNorm_integralKernelOperator (k : Lp ℂ 2 (μ.prod μ)) :
    schattenNorm (integralKernelOperator μ k) = ‖k‖ := by
  unfold integralKernelOperator
  rw [(hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose_spec.1]
  exact Lp.norm_compMeasurePreserving k (Measure.measurePreserving_swap (μ := μ) (ν := μ))

/-- Paper: Theorem C.3.7.1(2)(a), p. 708. If a square-integrable kernel is jointly
continuous at almost every diagonal point and its operator is nuclear, the diagonal
is integrable and its integral is the trace.
Deviation: The continuity and diagonal evaluation use a specified representative
of the L² kernel class. -/
theorem hilbertTrace_integralKernelOperator_of_ae_continuous {k : X × X → ℂ}
    (hk : MemLp k 2 (μ.prod μ))
    (hT : IsNuclearOperator (integralKernelOperator μ (hk.toLp k)).val)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt k (x, x)) :
    Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨(integralKernelOperator μ (hk.toLp k)).val, hT⟩ =
        ∫ x, k (x, x) ∂μ := by sorry

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- The rows of a square-integrable kernel are square-integrable almost everywhere. -/
private theorem ae_memLp_integralKernel_row (a : Lp ℂ 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun z ↦ a (x, z)) 2 μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).mp (Lp.memLp a)
  filter_upwards [h.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable a).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hx

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- The columns of a square-integrable kernel are square-integrable almost everywhere. -/
private theorem ae_memLp_integralKernel_column (b : Lp ℂ 2 (μ.prod μ)) :
    ∀ᵐ y ∂μ, MemLp (fun z ↦ b (z, y)) 2 μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable b)).mp (Lp.memLp b)
  filter_upwards [h.prod_left_ae] with y hy
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable b).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hy

/-- The kernel-to-operator correspondence in target-first coordinates is bijective. -/
private theorem bijective_integralKernelOperator : Function.Bijective (integralKernelOperator μ) := by
  let hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  let swap := Lp.compMeasurePreserving (E := ℂ) (p := 2) Prod.swap hswap
  have hswap_inv : Function.Involutive swap := by
    intro a
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (swap a) hswap,
      hswap.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving a hswap)] with p h₁ h₂
    exact h₁.trans h₂
  exact (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose.bijective.comp hswap_inv.bijective

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- Integrating a product of two square-integrable kernels over their shared variable
gives a square-integrable kernel, and the section products are integrable almost everywhere. -/
private theorem memLp_integralKernel_convolution (a b : Lp ℂ 2 (μ.prod μ)) :
    MemLp (fun p : X × X ↦ ∫ z, a (p.1, z) * b (z, p.2) ∂μ) 2 (μ.prod μ) ∧
      ∀ᵐ p ∂(μ.prod μ), Integrable (fun z ↦ a (p.1, z) * b (z, p.2)) μ := by
  have hrows := (Measure.quasiMeasurePreserving_fst (ν := μ)).ae
    (ae_memLp_integralKernel_row μ a)
  have hcols := (Measure.quasiMeasurePreserving_snd (μ := μ)).ae
    (ae_memLp_integralKernel_column μ b)
  have hmeas : StronglyMeasurable
      (fun q : (X × X) × X ↦ a (q.1.1, q.2) * b (q.2, q.1.2)) :=
    ((Lp.stronglyMeasurable a).comp_measurable
      (measurable_fst.fst.prodMk measurable_snd)).mul
      ((Lp.stronglyMeasurable b).comp_measurable
        (measurable_snd.prodMk measurable_fst.snd))
  let rowEnergy (x : X) := ∫ z, ‖a (x, z)‖ ^ 2 ∂μ
  let colEnergy (y : X) := ∫ z, ‖b (z, y)‖ ^ 2 ∂μ
  have ha : Integrable rowEnergy μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).mp
      (Lp.memLp a)).integral_prod_left
  have hb : Integrable colEnergy μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable b)).mp
      (Lp.memLp b)).integral_prod_right
  refine ⟨(memLp_two_iff_integrable_sq_norm
    hmeas.integral_prod_right'.aestronglyMeasurable).mpr ?_, ?_⟩
  · refine (ha.mul_prod hb).mono' (hmeas.integral_prod_right'.norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [hrows, hcols] with p hp hq
    have hle : ‖∫ z, a (p.1, z) * b (z, p.2) ∂μ‖ ≤
        Real.sqrt (rowEnergy p.1) * Real.sqrt (colEnergy p.2) := by
      calc
        _ ≤ ∫ z, ‖a (p.1, z) * b (z, p.2)‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ _ := by
          simpa [rowEnergy, colEnergy, norm_mul, Real.sqrt_eq_rpow] using
            integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
              (by simpa using hp) (by simpa using hq)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (Real.sqrt (rowEnergy p.1) * Real.sqrt (colEnergy p.2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = rowEnergy p.1 * colEnergy p.2 := by
        rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
          Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)]
  · filter_upwards [hrows, hcols] with p hp hq
    exact hp.integrable_mul hq

/-- The integral operator of a convolution of square-integrable kernels is the
composition of their integral operators. -/
private theorem integralKernelOperator_convolution (a b : Lp ℂ 2 (μ.prod μ))
    (hc : MemLp (fun p : X × X ↦ ∫ z, a (p.1, z) * b (z, p.2) ∂μ) 2 (μ.prod μ)) :
    (integralKernelOperator μ (hc.toLp _)).val =
      (integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  let g := (integralKernelOperator μ b).val f
  have hconv := Measure.ae_ae_of_ae_prod hc.coeFn_toLp
  filter_upwards [integralKernelOperator_apply μ (hc.toLp _) f,
    integralKernelOperator_apply μ a g, ae_memLp_integralKernel_row μ a, hconv] with x hx ha hrow hxy
  let integrand (p : X × X) := a (x, p.1) * b p * f p.2
  have hrowSq := (memLp_two_iff_integrable_sq_norm hrow.aestronglyMeasurable).mp hrow
  have hfSq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hbSq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable b)).mp (Lp.memLp b)
  have hmeas : StronglyMeasurable integrand :=
    (((Lp.stronglyMeasurable a).comp_measurable (measurable_const.prodMk measurable_fst)).mul
      (Lp.stronglyMeasurable b)).mul ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)
  have hint : Integrable integrand (μ.prod μ) := by
    refine (((hrowSq.mul_prod hfSq).add hbSq).const_mul (1 / 2 : ℝ)).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards with p
    dsimp [integrand]
    simp only [norm_mul]
    nlinarith [sq_nonneg (‖a (x, p.1)‖ * ‖f p.2‖ - ‖b p‖)]
  calc
    _ = ∫ y, (hc.toLp _ : Lp ℂ 2 (μ.prod μ)) (x, y) * f y ∂μ := hx.2
    _ = ∫ y, ∫ z, integrand (z, y) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hxy] with y hy
      rw [hy, ← integral_mul_const]
    _ = ∫ z, ∫ y, integrand (z, y) ∂μ ∂μ :=
      (integral_prod_symm integrand hint).symm.trans (integral_prod integrand hint)
    _ = ∫ z, a (x, z) * g z ∂μ := by
      apply integral_congr_ae
      filter_upwards [integralKernelOperator_apply μ b f] with z hz
      rw [hz.2, ← integral_const_mul]
      simp only [integrand, mul_assoc]
    _ = _ := ha.2.symm

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- The product of two square-integrable kernels with reversed arguments in the
second kernel is integrable on the product space. -/
private theorem integrable_integralKernel_mul_swap (a b : Lp ℂ 2 (μ.prod μ)) :
    Integrable (fun p : X × X ↦ a p * b p.swap) (μ.prod μ) := by
  have hb := (Lp.memLp b).comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  exact (Lp.memLp a).integrable_mul hb

/-- A nuclear endomorphism of a complex Hilbert space factors into two Hilbert-Schmidt
endomorphisms by taking a fourth root of its Gram operator. -/
private theorem exists_hilbertSchmidt_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    ∃ A B : hilbertSchmidtOperators H H, T = A.val.comp B.val := by
  let S := CFC.sqrt (T.adjoint * T)
  let B := CFC.sqrt S
  have hS : S * S = T.adjoint * T :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      T.isPositive_adjoint_comp_self)
  have hB : B * B = S := CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)
  have hadjS : S.adjoint = S :=
    IsSelfAdjoint.star_eq (IsSelfAdjoint.of_nonneg (show 0 ≤ S from CFC.sqrt_nonneg _))
  have hadjB : B.adjoint = B :=
    IsSelfAdjoint.star_eq (IsSelfAdjoint.of_nonneg (show 0 ≤ B from CFC.sqrt_nonneg _))
  have hnorm (x : H) : ‖T x‖ ≤ ‖S x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have heq : ⟪T x, T x⟫_ℂ = ⟪S x, S x⟫_ℂ := calc
      _ = ⟪x, (T.adjoint * T) x⟫_ℂ := (ContinuousLinearMap.adjoint_inner_right T x (T x)).symm
      _ = ⟪x, (S * S) x⟫_ℂ := by rw [hS]
      _ = _ := by
        simpa only [hadjS, mul_apply_eq_comp] using
          ContinuousLinearMap.adjoint_inner_right S x (S x)
    exact le_of_eq (by simpa only [inner_self_eq_norm_sq] using congrArg (RCLike.re (K := ℂ)) heq)
  -- Extend the map S x ↦ T x to the closure of the range of S, then project onto it.
  obtain ⟨U, hU, hUS⟩ : ∃ U : H →L[ℂ] H, ‖U‖ ≤ 1 ∧ U * S = T := by
    let V := S.toLinearMap.range.topologicalClosure
    let i : H →ₗ[ℂ] V := S.toLinearMap.codRestrict V
      (fun x ↦ S.toLinearMap.range.le_topologicalClosure ⟨x, rfl⟩)
    have hi : DenseRange i := by
      have hincl : DenseRange (Set.inclusion S.toLinearMap.range.le_topologicalClosure) :=
        (denseRange_inclusion_iff _).2 subset_rfl
      exact hincl.comp (show Function.Surjective S.toLinearMap.rangeRestrict from
        fun ⟨x, y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩).denseRange
        (continuous_inclusion _)
    let j := T.toLinearMap.extendOfNorm i
    have hbound (x : H) : ‖T.toLinearMap x‖ ≤ 1 * ‖i x‖ := by
      simpa [i] using hnorm x
    have hj : ‖j‖ ≤ 1 := LinearMap.opNorm_extendOfNorm_le hi zero_le_one hbound
    have hj_apply (x : H) : j (i x) = T x :=
      LinearMap.extendOfNorm_eq hi ⟨1, hbound⟩ x
    let U := j.comp V.orthogonalProjectionOnto
    refine ⟨U, (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_, ?_⟩
    · simpa only [mul_one] using
        mul_le_mul hj V.orthogonalProjectionOnto_norm_le
          (norm_nonneg V.orthogonalProjectionOnto) zero_le_one
    · ext x
      change j (V.orthogonalProjectionOnto (S x)) = T x
      exact (congrArg j (V.orthogonalProjectionOnto_mem_subspace_eq_self (i x))).trans (hj_apply x)
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hb_sum : Summable (fun i ↦ ‖B (b i)‖ ^ 2) := by
    refine ((isNuclearOperator_iff_summable_traceNorm_diagonal b T).mp hT).congr fun i ↦ ?_
    change (⟪b i, S (b i)⟫_ℂ).re = _
    rw [← hB]
    have heq : ⟪b i, (B * B) (b i)⟫_ℂ = ⟪B (b i), B (b i)⟫_ℂ := by
      simpa only [hadjB, mul_apply_eq_comp] using
        ContinuousLinearMap.adjoint_inner_right B (b i) (B (b i))
    rw [heq]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have ha_sum : Summable (fun i ↦ ‖(U * B) (b i)‖ ^ 2) := by
    refine hb_sum.of_nonneg_of_le (fun _ ↦ sq_nonneg _) fun i ↦ ?_
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (U.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hU)
  refine ⟨⟨U * B, (mem_hilbertSchmidtOperators_iff_summable_basis b _).mpr ha_sum⟩,
    ⟨B, (mem_hilbertSchmidtOperators_iff_summable_basis b _).mpr hb_sum⟩, ?_⟩
  change T = (U * B) * B
  rw [mul_assoc, hB, hUS]

/-- Paper: Theorem C.3.7.1(2)(b), p. 708. The trace of a nuclear composite of
two integral operators with square-integrable kernels is the product-space integral
of the first kernel times the second kernel with its variables reversed.
Deviation: The diagonal integral is written as a single product-space integral by Fubini. -/
theorem hilbertTrace_integralKernelOperator_comp (a b : Lp ℂ 2 (μ.prod μ))
    (h : IsNuclearOperator
      ((integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val)) :
    hilbertTrace ⟨(integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val, h⟩ =
      ∫ p : X × X, a p * b p.swap ∂(μ.prod μ) := by sorry

/-- Paper: Theorem C.3.7.1(2)(b), p. 708. A nuclear integral operator has
Hilbert-Schmidt factors whose kernel convolution represents the original kernel.
The convolution is defined almost everywhere on the diagonal, where it is
integrable and computes the trace.
Deviation: The smoothening is expressed by the factor-kernel convolution
described on pp. 707–708. -/
theorem exists_integralKernel_smoothening (k : Lp ℂ 2 (μ.prod μ))
    (hT : IsNuclearOperator (integralKernelOperator μ k).val) :
    ∃ a b : Lp ℂ 2 (μ.prod μ),
      (integralKernelOperator μ k).val =
        (integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val ∧
      let integrand (p : X × X) (z : X) := a (p.1, z) * b (z, p.2)
      let smoothened (p : X × X) := ∫ z, integrand p z ∂μ
      (∀ᵐ p ∂(μ.prod μ), Integrable (integrand p) μ ∧ smoothened p = k p) ∧
        (∀ᵐ x ∂μ, Integrable (integrand (x, x)) μ) ∧
        Integrable (fun x ↦ smoothened (x, x)) μ ∧
        hilbertTrace ⟨(integralKernelOperator μ k).val, hT⟩ =
          ∫ x, smoothened (x, x) ∂μ := by
  obtain ⟨A, B, hcomp⟩ :=
    exists_hilbertSchmidt_factorization (integralKernelOperator μ k).val hT
  obtain ⟨a, rfl⟩ := (bijective_integralKernelOperator μ).surjective A
  obtain ⟨b, rfl⟩ := (bijective_integralKernelOperator μ).surjective B
  obtain ⟨hc, hint⟩ := memLp_integralKernel_convolution μ a b
  have hkernel : hc.toLp _ = k := by
    apply (bijective_integralKernelOperator μ).injective
    exact Subtype.ext ((integralKernelOperator_convolution μ a b hc).trans hcomp.symm)
  have hdiag := integrable_integralKernel_mul_swap μ a b
  refine ⟨a, b, hcomp, ?_, hdiag.prod_right_ae, hdiag.integral_prod_left, ?_⟩
  · have hcoe := hc.coeFn_toLp
    rw [hkernel] at hcoe
    filter_upwards [hint, hcoe] with p h₁ h₂
    exact ⟨h₁, h₂.symm⟩
  · have hnuc : IsNuclearOperator
        ((integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val) := hcomp ▸ hT
    have htrace : (⟨(integralKernelOperator μ k).val, hT⟩ : nuclearEndomorphisms (Lp ℂ 2 μ)) =
        ⟨(integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val, hnuc⟩ :=
      Subtype.ext hcomp
    rw [htrace, hilbertTrace_integralKernelOperator_comp]
    exact integral_prod _ hdiag

end RiemannMasullo
