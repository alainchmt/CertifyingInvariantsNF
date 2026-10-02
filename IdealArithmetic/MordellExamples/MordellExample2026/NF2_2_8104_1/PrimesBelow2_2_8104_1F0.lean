
import IdealArithmetic.MordellExamples.MordellExample2026.NF2_2_8104_1.RI2_2_8104_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

namespace NF2_2_8104_1

set_option linter.all false

open Classical Polynomial

noncomputable section 

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![0, 1]] i)))

def P2P0 : CertificateIrreducibleZModOfList' 2 1 2 1 [0, 1] where
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
 g := ![![[1, 1]]]
 h' := ![![[0, 1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2 : FactorsPolyZMod [-2026, 0, 1] 2 2 where
 D := ![[0, 1], [0, 1]]; D' := ![[0, 1], [0, 1]]
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
  w := ![![2, 0], ![0, 1]]
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

def A3 : FactorsPolyZMod [-2026, 0, 1] 3 2 where
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![1, 1]] i)))

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![4, 1]] i)))

def P5P0 : CertificateIrreducibleZModOfList' 5 1 2 2 [1, 1] where
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
 g := ![![[], [4, 1]]]
 h' := ![![[0, 1], [1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P5P1 : CertificateIrreducibleZModOfList' 5 1 2 2 [4, 1] where
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
 g := ![![[], [1, 1]]]
 h' := ![![[0, 1], [1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A5 : FactorsPolyZMod [-2026, 0, 1] 5 2 where
 D := ![[1, 1], [4, 1]]; D' := ![[1, 1], [4, 1]]
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
  w := ![![5, 0], ![1, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C51 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A5.D 1) 5 where
  n := 1
  w := ![![5, 0], ![4, 1]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0], ![2030, 0]] i)))

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6], [0, 1]]
 g := ![![[0, 2], [0, 1]], ![[0, 5], [0, 6]]]
 h' := ![![[0, 6], [0, 3], [0, 1]], ![[0, 1], [0, 4], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A7 : FactorsPolyZMod [-2026, 0, 1] 7 1 where
 D := ![[4, 0, 1]]; D' := ![[4, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![2]
 n := ![2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P7P0

def C70 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A7.D 0) 7 where
  n := 2
  w := ![![7, 0], ![2030, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K7 : KummerData 7 ![I7N0] ![49] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A7
  C := by
    intro i
    match i with
    | 0 => exact C70
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 7 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0], ![2035, 0]] i)))

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 10], [0, 1]]
 g := ![![[0, 5], [], [1]], ![[0, 6], [], [1]]]
 h' := ![![[0, 10], [0, 4], [2], [0, 1]], ![[0, 1], [0, 7], [2], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [0, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A11 : FactorsPolyZMod [-2026, 0, 1] 11 1 where
 D := ![[9, 0, 1]]; D' := ![[9, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![3]
 n := ![2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P11P0

def C110 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A11.D 0) 11 where
  n := 2
  w := ![![11, 0], ![2035, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K11 : KummerData 11 ![I11N0] ![121] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A11
  C := by
    intro i
    match i with
    | 0 => exact C110
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 11 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0], ![2028, 0]] i)))

def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12], [0, 1]]
 g := ![![[], [4], [0, 1]], ![[], [4], [0, 12]]]
 h' := ![![[0, 12], [5], [0, 11], [0, 1]], ![[0, 1], [5], [0, 2], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [0, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A13 : FactorsPolyZMod [-2026, 0, 1] 13 1 where
 D := ![[2, 0, 1]]; D' := ![[2, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![3]
 n := ![2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P13P0

def C130 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A13.D 0) 13 where
  n := 2
  w := ![![13, 0], ![2028, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K13 : KummerData 13 ![I13N0] ![169] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A13
  C := by
    intro i
    match i with
    | 0 => exact C130
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 13 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0], ![2040, 0]] i)))

def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 16], [0, 1]]
 g := ![![[], [], [], [1]], ![[], [], [], [1]]]
 h' := ![![[0, 16], [13], [9], [3], [0, 1]], ![[0, 1], [13], [9], [3], [0, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [0, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A17 : FactorsPolyZMod [-2026, 0, 1] 17 1 where
 D := ![[14, 0, 1]]; D' := ![[14, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4]
 n := ![2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P17P0

def C170 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A17.D 0) 17 where
  n := 2
  w := ![![17, 0], ![2040, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K17 : KummerData 17 ![I17N0] ![289] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A17
  C := by
    intro i
    match i with
    | 0 => exact C170
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 17 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0], ![2033, 0]] i)))

def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 18], [0, 1]]
 g := ![![[0, 11], [], [], [1]], ![[0, 8], [], [], [1]]]
 h' := ![![[0, 18], [0, 7], [11], [12], [0, 1]], ![[0, 1], [0, 12], [11], [12], [0, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [0, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A19 : FactorsPolyZMod [-2026, 0, 1] 19 1 where
 D := ![[7, 0, 1]]; D' := ![[7, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4]
 n := ![2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P19P0

def C190 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A19.D 0) 19 where
  n := 2
  w := ![![19, 0], ![2033, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K19 : KummerData 19 ![I19N0] ![361] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A19
  C := by
    intro i
    match i with
    | 0 => exact C190
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 19 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0], ![5, 1]] i)))

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0], ![18, 1]] i)))

def P23P0 : CertificateIrreducibleZModOfList' 23 1 2 4 [5, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [9], [4], [18, 1]]]
 h' := ![![[0, 1], [1], [3], [2], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P23P1 : CertificateIrreducibleZModOfList' 23 1 2 4 [18, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [9], [4], [5, 1]]]
 h' := ![![[0, 1], [22], [20], [2], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A23 : FactorsPolyZMod [-2026, 0, 1] 23 2 where
 D := ![[5, 1], [18, 1]]; D' := ![[5, 1], [18, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4, 4]
 n := ![1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P23P0
  | 1 => exact P23P1

def C230 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A23.D 0) 23 where
  n := 1
  w := ![![23, 0], ![5, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C231 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A23.D 1) 23 where
  n := 1
  w := ![![23, 0], ![18, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K23 : KummerData 23 ![I23N0, I23N1] ![23, 23] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A23
  C := by
    intro i
    match i with
    | 0 => exact C230
    | 1 => exact C231
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 23 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0], ![5, 1]] i)))

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0], ![24, 1]] i)))

def P29P0 : CertificateIrreducibleZModOfList' 29 1 2 4 [5, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [23], [25, 24, 1]]]
 h' := ![![[0, 1], [1], [1], [20], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P29P1 : CertificateIrreducibleZModOfList' 29 1 2 4 [24, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [23], [25, 5, 1]]]
 h' := ![![[0, 1], [1], [28], [9], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A29 : FactorsPolyZMod [-2026, 0, 1] 29 2 where
 D := ![[5, 1], [24, 1]]; D' := ![[5, 1], [24, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4, 4]
 n := ![1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P29P0
  | 1 => exact P29P1

def C290 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A29.D 0) 29 where
  n := 1
  w := ![![29, 0], ![5, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C291 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A29.D 1) 29 where
  n := 1
  w := ![![29, 0], ![24, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K29 : KummerData 29 ![I29N0, I29N1] ![29, 29] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A29
  C := by
    intro i
    match i with
    | 0 => exact C290
    | 1 => exact C291
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 29 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0], ![2046, 0]] i)))

def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [20, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 30], [0, 1]]
 g := ![![[0, 14], [0, 4], [0, 28], [0, 1]], ![[0, 17], [0, 27], [0, 3], [0, 30]]]
 h' := ![![[0, 30], [0, 13], [0, 29], [0, 11], [0, 1]], ![[0, 1], [0, 18], [0, 2], [0, 20], [0, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [0, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A31 : FactorsPolyZMod [-2026, 0, 1] 31 1 where
 D := ![[20, 0, 1]]; D' := ![[20, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4]
 n := ![2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P31P0

def C310 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A31.D 0) 31 where
  n := 2
  w := ![![31, 0], ![2046, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K31 : KummerData 31 ![I31N0] ![961] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A31
  C := by
    intro i
    match i with
    | 0 => exact C310
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 31 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0], ![18, 1]] i)))

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0], ![19, 1]] i)))

def P37P0 : CertificateIrreducibleZModOfList' 37 1 2 5 [18, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [12], [], [19, 1]]]
 h' := ![![[0, 1], [36], [6], [7], [28], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P37P1 : CertificateIrreducibleZModOfList' 37 1 2 5 [19, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [12], [], [18, 1]]]
 h' := ![![[0, 1], [36], [31], [7], [28], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A37 : FactorsPolyZMod [-2026, 0, 1] 37 2 where
 D := ![[18, 1], [19, 1]]; D' := ![[18, 1], [19, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5, 5]
 n := ![1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P37P0
  | 1 => exact P37P1

def C370 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A37.D 0) 37 where
  n := 1
  w := ![![37, 0], ![18, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C371 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A37.D 1) 37 where
  n := 1
  w := ![![37, 0], ![19, 1]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K37 : KummerData 37 ![I37N0, I37N1] ![37, 37] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A37
  C := by
    intro i
    match i with
    | 0 => exact C370
    | 1 => exact C371
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 37 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0], ![2050, 0]] i)))

def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [24, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 40], [0, 1]]
 g := ![![[], [], [4], [], [1]], ![[], [], [4], [], [1]]]
 h' := ![![[0, 40], [32], [27], [0, 2], [17], [0, 1]], ![[0, 1], [32], [27], [0, 39], [17], [0, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [0, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A41 : FactorsPolyZMod [-2026, 0, 1] 41 1 where
 D := ![[24, 0, 1]]; D' := ![[24, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5]
 n := ![2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P41P0

def C410 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A41.D 0) 41 where
  n := 2
  w := ![![41, 0], ![2050, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K41 : KummerData 41 ![I41N0] ![1681] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A41
  C := by
    intro i
    match i with
    | 0 => exact C410
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 41 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0], ![2064, 0]] i)))

def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [38, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 42], [0, 1]]
 g := ![![[0, 17], [], [23], [], [1]], ![[0, 26], [], [23], [], [1]]]
 h' := ![![[0, 42], [0, 24], [29], [0, 25], [5], [0, 1]], ![[0, 1], [0, 19], [29], [0, 18], [5], [0, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [0, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A43 : FactorsPolyZMod [-2026, 0, 1] 43 1 where
 D := ![[38, 0, 1]]; D' := ![[38, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5]
 n := ![2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P43P0

def C430 : PrimeIdealKummer Table ![0, 1] ![1, 0] (A43.D 0) 43 where
  n := 2
  w := ![![43, 0], ![2064, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K43 : KummerData 43 ![I43N0] ![1849] where
  a := ![0, 1]
  z := ![1, 0]
  heq := timesTableT_eq_Table
  A := A43
  C := by
    intro i
    match i with
    | 0 => exact C430
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 43 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB46I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 45 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 45 (by omega)

def PB46I0 : PrimesBelowBoundCertificateInterval O 1 45 46 where
  m := 14
  g := ![2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
  hP := PB46I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K2)
    · convert (containsPrimesAbove_of_KummerData K3)
    · convert (containsPrimesAbove_of_KummerData K5)
    · convert (containsPrimesAbove_of_KummerData K7)
    · convert (containsPrimesAbove_of_KummerData K11)
    · convert (containsPrimesAbove_of_KummerData K13)
    · convert (containsPrimesAbove_of_KummerData K17)
    · convert (containsPrimesAbove_of_KummerData K19)
    · convert (containsPrimesAbove_of_KummerData K23)
    · convert (containsPrimesAbove_of_KummerData K29)
    · convert (containsPrimesAbove_of_KummerData K31)
    · convert (containsPrimesAbove_of_KummerData K37)
    · convert (containsPrimesAbove_of_KummerData K41)
    · convert (containsPrimesAbove_of_KummerData K43)
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2]
    · exact ![3, 3]
    · exact ![5, 5]
    · exact ![49]
    · exact ![121]
    · exact ![169]
    · exact ![289]
    · exact ![361]
    · exact ![23, 23]
    · exact ![29, 29]
    · exact ![961]
    · exact ![37, 37]
    · exact ![1681]
    · exact ![1849]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K2)
    · exact (card_quot_of_KummerData K3)
    · exact (card_quot_of_KummerData K5)
    · exact (card_quot_of_KummerData K7)
    · exact (card_quot_of_KummerData K11)
    · exact (card_quot_of_KummerData K13)
    · exact (card_quot_of_KummerData K17)
    · exact (card_quot_of_KummerData K19)
    · exact (card_quot_of_KummerData K23)
    · exact (card_quot_of_KummerData K29)
    · exact (card_quot_of_KummerData K31)
    · exact (card_quot_of_KummerData K37)
    · exact (card_quot_of_KummerData K41)
    · exact (card_quot_of_KummerData K43)
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I23N0, I23N1, I29N0, I29N1, I37N0, I37N1]
  Il := ![[I2N0, I2N0], [I3N0, I3N1], [I5N0, I5N1], [], [], [], [], [], [I23N0, I23N1], [I29N0, I29N1], [], [I37N0, I37N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp

end

end NF2_2_8104_1
