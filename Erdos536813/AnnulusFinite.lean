import Erdos536813.FiniteGamma

namespace Erdos536813

/-!
## First concrete finite annulus certificate: `T = 120`

At `T = 120`,
`L23 120 = floor(log_2 120) + floor(log_3 120) + 1 = 11`,
and the exact annulus maximum is at most `8`.
Thus every Gamma-free annulus family has deficit at least three.
-/

/-- Exhaustive kernel computation for the annulus at `T = 120`. -/
theorem fiveAnnulus_120_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 120) 8 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 120` annulus has size at most `8`. -/
theorem gammaFree_fiveAnnulus_120_length_le_eight
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 120)) :
    S.length ≤ 8 := by
  exact gammaFree_length_le_of_subsetBoundBool
    fiveAnnulus_120_subset_bound_bool hGamma hSub

/-- The `T = 120` annulus has deficit at least three relative to `L23 120`. -/
theorem gammaFree_fiveAnnulus_120_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 120)) :
    S.length + 3 ≤ L23 120 := by
  have hLen : S.length ≤ 8 :=
    gammaFree_fiveAnnulus_120_length_le_eight hGamma hSub
  norm_num [L23, Nat.log]
  omega


/-!
## Remaining critical finite annulus states

The annulus board changes only at finitely many critical values in
`120 ≤ T ≤ 728`.  The `T = 120` state was certified above.  Here we
kernel-check the remaining critical boards, always using the weaker uniform
target `L23 T - 3`; some states in fact have a larger exact deficit.

These are concrete exhaustive computations over all sublists of the finite
annulus list.
-/

/-- Exhaustive finite annulus certificate at `T = 128`. -/
theorem fiveAnnulus_128_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 128) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 128` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_128_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 128)) :
    S.length + 3 ≤ L23 128 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_128_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 135`. -/
theorem fiveAnnulus_135_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 135) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 135` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_135_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 135)) :
    S.length + 3 ≤ L23 135 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_135_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 144`. -/
theorem fiveAnnulus_144_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 144) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 144` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_144_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 144)) :
    S.length + 3 ≤ L23 144 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_144_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 160`. -/
theorem fiveAnnulus_160_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 160) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 160` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_160_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 160)) :
    S.length + 3 ≤ L23 160 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_160_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 162`. -/
theorem fiveAnnulus_162_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 162) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 162` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_162_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 162)) :
    S.length + 3 ≤ L23 162 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_162_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 180`. -/
theorem fiveAnnulus_180_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 180) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 180` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_180_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 180)) :
    S.length + 3 ≤ L23 180 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_180_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 192`. -/
theorem fiveAnnulus_192_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 192) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 192` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_192_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 192)) :
    S.length + 3 ≤ L23 192 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_192_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 216`. -/
theorem fiveAnnulus_216_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 216) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 216` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_216_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 216)) :
    S.length + 3 ≤ L23 216 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_216_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 240`. -/
theorem fiveAnnulus_240_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 240) 9 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 240` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_240_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 240)) :
    S.length + 3 ≤ L23 240 := by
  have hLen : S.length ≤ 9 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_240_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 243`. -/
theorem fiveAnnulus_243_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 243) 10 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 243` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_243_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 243)) :
    S.length + 3 ≤ L23 243 := by
  have hLen : S.length ≤ 10 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_243_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 256`. -/
theorem fiveAnnulus_256_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 256) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 256` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_256_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 256)) :
    S.length + 3 ≤ L23 256 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_256_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 270`. -/
theorem fiveAnnulus_270_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 270) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 270` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_270_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 270)) :
    S.length + 3 ≤ L23 270 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_270_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 288`. -/
theorem fiveAnnulus_288_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 288) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 288` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_288_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 288)) :
    S.length + 3 ≤ L23 288 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_288_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 320`. -/
theorem fiveAnnulus_320_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 320) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 320` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_320_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 320)) :
    S.length + 3 ≤ L23 320 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_320_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 324`. -/
theorem fiveAnnulus_324_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 324) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 324` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_324_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 324)) :
    S.length + 3 ≤ L23 324 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_324_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 360`. -/
theorem fiveAnnulus_360_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 360) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 360` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_360_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 360)) :
    S.length + 3 ≤ L23 360 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_360_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 384`. -/
theorem fiveAnnulus_384_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 384) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 384` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_384_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 384)) :
    S.length + 3 ≤ L23 384 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_384_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 405`. -/
theorem fiveAnnulus_405_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 405) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 405` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_405_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 405)) :
    S.length + 3 ≤ L23 405 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_405_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 432`. -/
theorem fiveAnnulus_432_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 432) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 432` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_432_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 432)) :
    S.length + 3 ≤ L23 432 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_432_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 480`. -/
theorem fiveAnnulus_480_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 480) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 480` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_480_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 480)) :
    S.length + 3 ≤ L23 480 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_480_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 486`. -/
theorem fiveAnnulus_486_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 486) 11 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 486` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_486_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 486)) :
    S.length + 3 ≤ L23 486 := by
  have hLen : S.length ≤ 11 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_486_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 512`. -/
theorem fiveAnnulus_512_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 512) 12 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 512` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_512_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 512)) :
    S.length + 3 ≤ L23 512 := by
  have hLen : S.length ≤ 12 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_512_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 540`. -/
theorem fiveAnnulus_540_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 540) 12 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 540` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_540_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 540)) :
    S.length + 3 ≤ L23 540 := by
  have hLen : S.length ≤ 12 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_540_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 576`. -/
theorem fiveAnnulus_576_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 576) 12 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 576` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_576_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 576)) :
    S.length + 3 ≤ L23 576 := by
  have hLen : S.length ≤ 12 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_576_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 640`. -/
theorem fiveAnnulus_640_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 640) 12 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 640` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_640_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 640)) :
    S.length + 3 ≤ L23 640 := by
  have hLen : S.length ≤ 12 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_640_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 648`. -/
theorem fiveAnnulus_648_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 648) 12 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 648` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_648_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 648)) :
    S.length + 3 ≤ L23 648 := by
  have hLen : S.length ≤ 12 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_648_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega

/-- Exhaustive finite annulus certificate at `T = 720`. -/
theorem fiveAnnulus_720_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 720) 12 = true := by
  native_decide

/-- Every Gamma-free subset of the `T = 720` annulus has deficit at least three. -/
theorem gammaFree_fiveAnnulus_720_deficit_three
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 720)) :
    S.length + 3 ≤ L23 720 := by
  have hLen : S.length ≤ 12 := by
    exact gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_720_subset_bound_bool hGamma hSub
  norm_num [L23, Nat.log]
  omega


/-!
## Efficient finite-range interpolation

The critical-state certificates above are already kernel-checked.  To fill
the gaps between them without expanding the very large `FiveAnnulusList`,
we use the fixed rectangle `0 ≤ i < 10`, `0 ≤ j < 6`.  Every annulus point
with `T ≤ 728` lies in this rectangle, since `2^10 > 728` and `3^6 > 728`.

This gives a small executable representation whose equality between
successive critical states is cheap for the kernel to check.
-/

/-- Every annulus point with `T ≤ 728` has `i < 10`. -/
theorem fiveAnnulus_i_lt_ten_of_le_728
    {T : Nat}
    {p : Erdos536.GridPoint}
    (hT : T ≤ 728)
    (hp : InFiveAnnulus T p) :
    p.i < 10 := by
  by_contra h
  have hi : 10 ≤ p.i := Nat.le_of_not_gt h
  have hPowMono : 2 ^ 10 ≤ 2 ^ p.i :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hi
  have h3pos : 0 < 3 ^ p.j :=
    Nat.pow_pos (by decide : 0 < (3 : Nat))
  have hPowToValue :
      2 ^ p.i ≤ Erdos536.fiberValue 1 p := by
    have hmul := Nat.le_mul_of_pos_right (2 ^ p.i) h3pos
    simpa [Erdos536.fiberValue] using hmul
  have hBig : 1024 ≤ Erdos536.fiberValue 1 p := by
    norm_num at hPowMono
    exact Nat.le_trans hPowMono hPowToValue
  have hValueLeT : Erdos536.fiberValue 1 p ≤ T := hp.1
  omega

/-- Every annulus point with `T ≤ 728` has `j < 6`. -/
theorem fiveAnnulus_j_lt_six_of_le_728
    {T : Nat}
    {p : Erdos536.GridPoint}
    (hT : T ≤ 728)
    (hp : InFiveAnnulus T p) :
    p.j < 6 := by
  by_contra h
  have hj : 6 ≤ p.j := Nat.le_of_not_gt h
  have hPowMono : 3 ^ 6 ≤ 3 ^ p.j :=
    Nat.pow_le_pow_right (by decide : 0 < (3 : Nat)) hj
  have h2pos : 0 < 2 ^ p.i :=
    Nat.pow_pos (by decide : 0 < (2 : Nat))
  have hPowToValue :
      3 ^ p.j ≤ Erdos536.fiberValue 1 p := by
    have hmul := Nat.le_mul_of_pos_left (3 ^ p.j) h2pos
    simpa [Erdos536.fiberValue, Nat.mul_comm] using hmul
  have hBig : 729 ≤ Erdos536.fiberValue 1 p := by
    norm_num at hPowMono
    exact Nat.le_trans hPowMono hPowToValue
  have hValueLeT : Erdos536.fiberValue 1 p ≤ T := hp.1
  omega

/-- Executable Boolean form of five-annulus membership. -/
def InFiveAnnulusBool
    (T : Nat)
    (p : Erdos536.GridPoint) : Bool :=
  decide (Erdos536.fiberValue 1 p ≤ T) &&
    decide (T < 5 * Erdos536.fiberValue 1 p)

/-- The Boolean annulus predicate is exact. -/
theorem inFiveAnnulusBool_eq_true_iff
    (T : Nat)
    (p : Erdos536.GridPoint) :
    InFiveAnnulusBool T p = true ↔ InFiveAnnulus T p := by
  simp [InFiveAnnulusBool, InFiveAnnulus]

/-- Small executable annulus list sufficient throughout `T ≤ 728`. -/
def SmallFiveAnnulusList (T : Nat) : List Erdos536.GridPoint :=
  (Erdos536.GridPoint.rect 10 6).filter
    (fun p => InFiveAnnulusBool T p)

/-- Exact membership in the small annulus representation for `T ≤ 728`. -/
theorem mem_smallFiveAnnulusList
    {T : Nat}
    (hT : T ≤ 728)
    {p : Erdos536.GridPoint} :
    p ∈ SmallFiveAnnulusList T ↔ InFiveAnnulus T p := by
  constructor
  · intro hp
    rcases List.mem_filter.mp hp with ⟨_hRect, hAnnBool⟩
    exact (inFiveAnnulusBool_eq_true_iff T p).1 hAnnBool
  · intro hp
    apply List.mem_filter.mpr
    constructor
    · rw [Erdos536.GridPoint.mem_rect]
      exact ⟨fiveAnnulus_i_lt_ten_of_le_728 hT hp,
        fiveAnnulus_j_lt_six_of_le_728 hT hp⟩
    · exact (inFiveAnnulusBool_eq_true_iff T p).2 hp

/-- Left critical representative for the finite annulus range. -/
def FiniteAnnulusRepresentative (T : Nat) : Nat :=
  if T < 128 then 120 else
    if T < 135 then 128 else
      if T < 144 then 135 else
        if T < 160 then 144 else
          if T < 162 then 160 else
            if T < 180 then 162 else
              if T < 192 then 180 else
                if T < 216 then 192 else
                  if T < 240 then 216 else
                    if T < 243 then 240 else
                      if T < 256 then 243 else
                        if T < 270 then 256 else
                          if T < 288 then 270 else
                            if T < 320 then 288 else
                              if T < 324 then 320 else
                                if T < 360 then 324 else
                                  if T < 384 then 360 else
                                    if T < 405 then 384 else
                                      if T < 432 then 405 else
                                        if T < 480 then 432 else
                                          if T < 486 then 480 else
                                            if T < 512 then 486 else
                                              if T < 540 then 512 else
                                                if T < 576 then 540 else
                                                  if T < 640 then 576 else
                                                    if T < 648 then 640 else
                                                      if T < 720 then 648 else
                                                        720


/--
The critical representative carries the already-certified deficit-three
bound.  This theorem only dispatches to the corresponding critical-state
theorem; it performs no new exhaustive search.
-/
theorem gammaFree_representative_deficit_three
    (T : Nat)
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub :
      S.Subset (FiveAnnulusList (FiniteAnnulusRepresentative T))) :
    S.length + 3 ≤ L23 (FiniteAnnulusRepresentative T) := by
  by_cases h128 : T < 128
  · have hSub' : S.Subset (FiveAnnulusList 120) := by
      simpa [FiniteAnnulusRepresentative, h128] using hSub
    have h := gammaFree_fiveAnnulus_120_deficit_three hGamma hSub'
    simpa [FiniteAnnulusRepresentative, h128] using h
  · by_cases h135 : T < 135
    · have hSub' : S.Subset (FiveAnnulusList 128) := by
        simpa [FiniteAnnulusRepresentative, h128, h135] using hSub
      have h := gammaFree_fiveAnnulus_128_deficit_three hGamma hSub'
      simpa [FiniteAnnulusRepresentative, h128, h135] using h
    · by_cases h144 : T < 144
      · have hSub' : S.Subset (FiveAnnulusList 135) := by
          simpa [FiniteAnnulusRepresentative, h128, h135, h144] using hSub
        have h := gammaFree_fiveAnnulus_135_deficit_three hGamma hSub'
        simpa [FiniteAnnulusRepresentative, h128, h135, h144] using h
      · by_cases h160 : T < 160
        · have hSub' : S.Subset (FiveAnnulusList 144) := by
            simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160] using hSub
          have h := gammaFree_fiveAnnulus_144_deficit_three hGamma hSub'
          simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160] using h
        · by_cases h162 : T < 162
          · have hSub' : S.Subset (FiveAnnulusList 160) := by
              simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162] using hSub
            have h := gammaFree_fiveAnnulus_160_deficit_three hGamma hSub'
            simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162] using h
          · by_cases h180 : T < 180
            · have hSub' : S.Subset (FiveAnnulusList 162) := by
                simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180] using hSub
              have h := gammaFree_fiveAnnulus_162_deficit_three hGamma hSub'
              simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180] using h
            · by_cases h192 : T < 192
              · have hSub' : S.Subset (FiveAnnulusList 180) := by
                  simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192] using hSub
                have h := gammaFree_fiveAnnulus_180_deficit_three hGamma hSub'
                simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192] using h
              · by_cases h216 : T < 216
                · have hSub' : S.Subset (FiveAnnulusList 192) := by
                    simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216] using hSub
                  have h := gammaFree_fiveAnnulus_192_deficit_three hGamma hSub'
                  simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216] using h
                · by_cases h240 : T < 240
                  · have hSub' : S.Subset (FiveAnnulusList 216) := by
                      simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240] using hSub
                    have h := gammaFree_fiveAnnulus_216_deficit_three hGamma hSub'
                    simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240] using h
                  · by_cases h243 : T < 243
                    · have hSub' : S.Subset (FiveAnnulusList 240) := by
                        simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243] using hSub
                      have h := gammaFree_fiveAnnulus_240_deficit_three hGamma hSub'
                      simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243] using h
                    · by_cases h256 : T < 256
                      · have hSub' : S.Subset (FiveAnnulusList 243) := by
                          simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256] using hSub
                        have h := gammaFree_fiveAnnulus_243_deficit_three hGamma hSub'
                        simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256] using h
                      · by_cases h270 : T < 270
                        · have hSub' : S.Subset (FiveAnnulusList 256) := by
                            simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270] using hSub
                          have h := gammaFree_fiveAnnulus_256_deficit_three hGamma hSub'
                          simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270] using h
                        · by_cases h288 : T < 288
                          · have hSub' : S.Subset (FiveAnnulusList 270) := by
                              simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288] using hSub
                            have h := gammaFree_fiveAnnulus_270_deficit_three hGamma hSub'
                            simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288] using h
                          · by_cases h320 : T < 320
                            · have hSub' : S.Subset (FiveAnnulusList 288) := by
                                simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320] using hSub
                              have h := gammaFree_fiveAnnulus_288_deficit_three hGamma hSub'
                              simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320] using h
                            · by_cases h324 : T < 324
                              · have hSub' : S.Subset (FiveAnnulusList 320) := by
                                  simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324] using hSub
                                have h := gammaFree_fiveAnnulus_320_deficit_three hGamma hSub'
                                simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324] using h
                              · by_cases h360 : T < 360
                                · have hSub' : S.Subset (FiveAnnulusList 324) := by
                                    simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360] using hSub
                                  have h := gammaFree_fiveAnnulus_324_deficit_three hGamma hSub'
                                  simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360] using h
                                · by_cases h384 : T < 384
                                  · have hSub' : S.Subset (FiveAnnulusList 360) := by
                                      simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384] using hSub
                                    have h := gammaFree_fiveAnnulus_360_deficit_three hGamma hSub'
                                    simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384] using h
                                  · by_cases h405 : T < 405
                                    · have hSub' : S.Subset (FiveAnnulusList 384) := by
                                        simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405] using hSub
                                      have h := gammaFree_fiveAnnulus_384_deficit_three hGamma hSub'
                                      simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405] using h
                                    · by_cases h432 : T < 432
                                      · have hSub' : S.Subset (FiveAnnulusList 405) := by
                                          simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432] using hSub
                                        have h := gammaFree_fiveAnnulus_405_deficit_three hGamma hSub'
                                        simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432] using h
                                      · by_cases h480 : T < 480
                                        · have hSub' : S.Subset (FiveAnnulusList 432) := by
                                            simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480] using hSub
                                          have h := gammaFree_fiveAnnulus_432_deficit_three hGamma hSub'
                                          simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480] using h
                                        · by_cases h486 : T < 486
                                          · have hSub' : S.Subset (FiveAnnulusList 480) := by
                                              simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486] using hSub
                                            have h := gammaFree_fiveAnnulus_480_deficit_three hGamma hSub'
                                            simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486] using h
                                          · by_cases h512 : T < 512
                                            · have hSub' : S.Subset (FiveAnnulusList 486) := by
                                                simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512] using hSub
                                              have h := gammaFree_fiveAnnulus_486_deficit_three hGamma hSub'
                                              simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512] using h
                                            · by_cases h540 : T < 540
                                              · have hSub' : S.Subset (FiveAnnulusList 512) := by
                                                  simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540] using hSub
                                                have h := gammaFree_fiveAnnulus_512_deficit_three hGamma hSub'
                                                simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540] using h
                                              · by_cases h576 : T < 576
                                                · have hSub' : S.Subset (FiveAnnulusList 540) := by
                                                    simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576] using hSub
                                                  have h := gammaFree_fiveAnnulus_540_deficit_three hGamma hSub'
                                                  simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576] using h
                                                · by_cases h640 : T < 640
                                                  · have hSub' : S.Subset (FiveAnnulusList 576) := by
                                                      simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576, h640] using hSub
                                                    have h := gammaFree_fiveAnnulus_576_deficit_three hGamma hSub'
                                                    simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576, h640] using h
                                                  · by_cases h648 : T < 648
                                                    · have hSub' : S.Subset (FiveAnnulusList 640) := by
                                                        simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576, h640, h648] using hSub
                                                      have h := gammaFree_fiveAnnulus_640_deficit_three hGamma hSub'
                                                      simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576, h640, h648] using h
                                                    · by_cases h720 : T < 720
                                                      · have hSub' : S.Subset (FiveAnnulusList 648) := by
                                                          simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576, h640, h648, h720] using hSub
                                                        have h := gammaFree_fiveAnnulus_648_deficit_three hGamma hSub'
                                                        simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576, h640, h648, h720] using h
                                                      · have hSub' : S.Subset (FiveAnnulusList 720) := by
                                                          simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576, h640, h648, h720] using hSub
                                                        have h := gammaFree_fiveAnnulus_720_deficit_three hGamma hSub'
                                                        simpa [FiniteAnnulusRepresentative, h128, h135, h144, h160, h162, h180, h192, h216, h240, h243, h256, h270, h288, h320, h324, h360, h384, h405, h432, h480, h486, h512, h540, h576, h640, h648, h720] using h

set_option maxHeartbeats 1000000 in
/--
For every `120 ≤ T ≤ 728`, the small annulus board and the logarithmic
baseline agree exactly with those at the chosen critical representative.
Because the board has only 60 possible grid points, this finite kernel check
is inexpensive.
-/
theorem finiteAnnulusRepresentative_small_data
    {T : Nat}
    (hLow : 120 ≤ T)
    (hHigh : T ≤ 728) :
    SmallFiveAnnulusList T =
        SmallFiveAnnulusList (FiniteAnnulusRepresentative T) ∧
      L23 T = L23 (FiniteAnnulusRepresentative T) := by
  interval_cases T <;> native_decide

/--
Uniform finite annulus lemma on `120 ≤ T ≤ 728`.
-/
theorem gammaFree_annulus_finite_deficit_three
    {T : Nat}
    (hLow : 120 ≤ T)
    (hHigh : T ≤ 728)
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSAnn : ∀ p ∈ S, InFiveAnnulus T p) :
    S.length + 3 ≤ L23 T := by
  have hData :=
    finiteAnnulusRepresentative_small_data hLow hHigh
  have hSubSmallT : S.Subset (SmallFiveAnnulusList T) := by
    intro p hp
    exact (mem_smallFiveAnnulusList hHigh).2 (hSAnn p hp)
  have hSubSmallR :
      S.Subset (SmallFiveAnnulusList (FiniteAnnulusRepresentative T)) := by
    intro p hp
    rw [← hData.1]
    exact hSubSmallT hp
  have hSubBigR :
      S.Subset (FiveAnnulusList (FiniteAnnulusRepresentative T)) := by
    intro p hp
    have hpSmall :
        p ∈ SmallFiveAnnulusList (FiniteAnnulusRepresentative T) :=
      hSubSmallR hp
    apply (mem_fiveAnnulusList).2
    rcases List.mem_filter.mp hpSmall with ⟨_, hAnnBool⟩
    exact (inFiveAnnulusBool_eq_true_iff
      (FiniteAnnulusRepresentative T) p).1 hAnnBool
  have hRep :=
    gammaFree_representative_deficit_three T hGamma hSubBigR
  rw [hData.2]
  exact hRep

/-!
## Strong annulus lemma for every `T ≥ 120`
-/

/--
Every Gamma-free family contained in the five-annulus at scale `T ≥ 120`
has deficit at least three relative to `L23 T`.
-/
theorem gammaFree_annulus_deficit_three
    {T : Nat}
    (hT : 120 ≤ T)
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSAnn : ∀ p ∈ S, InFiveAnnulus T p) :
    S.length + 3 ≤ L23 T := by
  by_cases hFinite : T ≤ 728
  · exact gammaFree_annulus_finite_deficit_three
      hT hFinite hGamma hSAnn
  · have hLarge : 729 ≤ T := by
      omega
    exact gammaFree_annulus_large_deficit_three
      hLarge hGamma hSAnn

/-- List-subset formulation of the strong annulus lemma. -/
theorem gammaFree_subset_fiveAnnulus_deficit_three
    {T : Nat}
    (hT : 120 ≤ T)
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList T)) :
    S.length + 3 ≤ L23 T := by
  apply gammaFree_annulus_deficit_three hT hGamma
  intro p hp
  exact (mem_fiveAnnulusList).1 (hSub hp)

end Erdos536813
