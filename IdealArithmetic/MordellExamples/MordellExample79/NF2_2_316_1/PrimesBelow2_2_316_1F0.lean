
import IdealArithmetic.MordellExamples.MordellExample79.NF2_2_316_1.RI2_2_316_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

namespace NF2_2_316_1

set_option linter.all false

open Classical Polynomial

noncomputable section 

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![1, 1]] i)))

def P2P0 : CertificateIrreducibleZModOfList' 2 1 2 1 [1, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[0, 1]]]
 h' := ![![[0, 1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2 : FactorsPolyZMod [-79, 0, 1] 2 2 where
 D := ![[1, 1], [1, 1]]; D' := ![[1, 1], [1, 1]]
 heqm := by decide
 hProd := by decide
 s := ![1, 1]
 n := ![1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2P0
  | 1 => exact P2P0

def C20 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A2.D 0) 2 where
  n := 1
  w := ![![2, 0], ![1, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2 : KummerData 2 ![I2N0, I2N0] ![2, 2] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A2
  C := by
    intro i
    match i with
    | 0 => exact C20
    | 1 => exact C20
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0], ![1, 1]] i)))

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0], ![2, 1]] i)))

def P3P0 : CertificateIrreducibleZModOfList' 3 1 2 1 [1, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[0, 2, 1]]]
 h' := ![![[0, 1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3P1 : CertificateIrreducibleZModOfList' 3 1 2 1 [2, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[0, 1, 1]]]
 h' := ![![[0, 1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3 : FactorsPolyZMod [-79, 0, 1] 3 2 where
 D := ![[1, 1], [2, 1]]; D' := ![[1, 1], [2, 1]]
 heqm := by decide
 hProd := by decide
 s := ![1, 1]
 n := ![1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3P0
  | 1 => exact P3P1

def C30 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A3.D 0) 3 where
  n := 1
  w := ![![3, 0], ![1, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C31 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A3.D 1) 3 where
  n := 1
  w := ![![3, 0], ![2, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3 : KummerData 3 ![I3N0, I3N1] ![3, 3] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A3
  C := by
    intro i
    match i with
    | 0 => exact C30
    | 1 => exact C31
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![2, 1]] i)))

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![3, 1]] i)))

def P5P0 : CertificateIrreducibleZModOfList' 5 1 2 2 [2, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [3, 1]]]
 h' := ![![[0, 1], [4], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P5P1 : CertificateIrreducibleZModOfList' 5 1 2 2 [3, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2, 1]]]
 h' := ![![[0, 1], [4], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A5 : FactorsPolyZMod [-79, 0, 1] 5 2 where
 D := ![[2, 1], [3, 1]]; D' := ![[2, 1], [3, 1]]
 heqm := by decide
 hProd := by decide
 s := ![2, 2]
 n := ![1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P5P0
  | 1 => exact P5P1

def C50 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A5.D 0) 5 where
  n := 1
  w := ![![5, 0], ![2, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C51 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A5.D 1) 5 where
  n := 1
  w := ![![5, 0], ![3, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K5 : KummerData 5 ![I5N0, I5N1] ![5, 5] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A5
  C := by
    intro i
    match i with
    | 0 => exact C50
    | 1 => exact C51
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 5 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0], ![3, 1]] i)))

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0], ![4, 1]] i)))

def P7P0 : CertificateIrreducibleZModOfList' 7 1 2 2 [3, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2, 4, 1]]]
 h' := ![![[0, 1], [1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 1 2 2 [4, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2, 3, 1]]]
 h' := ![![[0, 1], [6], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A7 : FactorsPolyZMod [-79, 0, 1] 7 2 where
 D := ![[3, 1], [4, 1]]; D' := ![[3, 1], [4, 1]]
 heqm := by decide
 hProd := by decide
 s := ![2, 2]
 n := ![1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P7P0
  | 1 => exact P7P1

def C70 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A7.D 0) 7 where
  n := 1
  w := ![![7, 0], ![3, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C71 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A7.D 1) 7 where
  n := 1
  w := ![![7, 0], ![4, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K7 : KummerData 7 ![I7N0, I7N1] ![7, 7] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A7
  C := by
    intro i
    match i with
    | 0 => exact C70
    | 1 => exact C71
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 7 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB9I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 8 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 8 (by omega)

def PB9I0 : PrimesBelowBoundCertificateInterval O 1 8 9 where
  m := 4
  g := ![2, 2, 2, 2]
  P := ![2, 3, 5, 7]
  hP := PB9I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K2)
    · convert (containsPrimesAbove_of_KummerData K3)
    · convert (containsPrimesAbove_of_KummerData K5)
    · convert (containsPrimesAbove_of_KummerData K7)
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2]
    · exact ![3, 3]
    · exact ![5, 5]
    · exact ![7, 7]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K2)
    · exact (card_quot_of_KummerData K3)
    · exact (card_quot_of_KummerData K5)
    · exact (card_quot_of_KummerData K7)
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1]
  Il := ![[I2N0, I2N0], [I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp

end

end NF2_2_316_1
