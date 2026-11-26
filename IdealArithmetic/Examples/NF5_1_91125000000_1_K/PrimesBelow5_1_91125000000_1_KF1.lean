
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![15747, 551, 116, 0, 0]] i)))

def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [27, 26, 16, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 19, 16, 16, 22], [9, 2, 21, 25, 2], [10, 14, 2, 16, 26], [2, 22, 19, 1, 8], [0, 1]]
 g := ![![[4, 26, 23, 10, 28], [5, 3, 20, 24], [0, 0, 1], []], ![[12, 11, 8, 27, 13, 2, 4, 25], [13, 27, 7, 5], [19, 21, 13, 12, 24, 24, 22, 5], [3, 14, 9, 14, 1, 21, 3, 5]], ![[16, 16, 6, 21, 10, 2, 7, 11], [19, 1, 11, 13], [25, 16, 17, 4, 19, 18, 28, 3], [11, 1, 26, 21, 13, 0, 10, 8]], ![[21, 26, 15, 27, 16, 27, 25, 19], [0, 9, 17, 23], [17, 8, 8, 3, 21, 6, 25, 26], [14, 18, 26, 25, 9, 12, 26, 2]], ![[20, 13, 14, 9, 20, 5, 4, 17], [13, 3, 11, 9], [9, 25, 20, 12, 9, 3, 6, 21], [27, 8, 1, 12, 19, 18, 18, 19]]]
 h' := ![![[8, 19, 16, 16, 22], [10, 21, 27, 2, 17], [0, 0, 2, 3, 13], [0, 0, 0, 1], [0, 1]], ![[9, 2, 21, 25, 2], [3, 14, 7, 6, 19], [21, 14, 12, 1, 18], [25, 2, 3, 23, 22], [8, 19, 16, 16, 22]], ![[10, 14, 2, 16, 26], [2, 6, 17, 0, 22], [15, 5, 10, 2, 10], [26, 28, 15, 16, 25], [9, 2, 21, 25, 2]], ![[2, 22, 19, 1, 8], [24, 14, 25, 10, 19], [13, 11, 4, 20, 20], [13, 15, 11, 16, 28], [10, 14, 2, 16, 26]], ![[0, 1], [3, 3, 11, 11, 10], [21, 28, 1, 3, 26], [4, 13, 0, 2, 12], [2, 22, 19, 1, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 24, 17, 24], [], [], []]
 b := ![[], [20, 18, 13, 15, 20], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A29 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 29 1 where
 D := ![[27, 26, 16, 0, 0, 1]]; D' := ![[27, 26, 16, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P29P0

def C290 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A29.D 0) 29 where
  n := 5
  w := ![![29, 0, 0, 0, 0], ![15747, 551, 116, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K29 : KummerData 29 ![I29N0] ![20511149] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A29
  C := by
    intro i
    match i with
    | 0 => exact C290
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 29 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![19, 1, 0, 0, 0]] i)))

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![22, 1, 0, 0, 0]] i)))

def I31N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] i)))

def I31N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![25, 1, 0, 0, 0]] i)))

def P31P0 : CertificateIrreducibleZModOfList' 31 1 2 4 [4, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [8], [4], [16, 27, 1]]]
 h' := ![![[0, 1], [30], [15], [29], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P31P1 : CertificateIrreducibleZModOfList' 31 1 2 4 [19, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [18], [2], [20, 12, 1]]]
 h' := ![![[0, 1], [30], [24], [23], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P31P2 : CertificateIrreducibleZModOfList' 31 1 2 4 [22, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [7], [8], [19, 9, 1]]]
 h' := ![![[0, 1], [1], [10], [16], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P31P3 : CertificateIrreducibleZModOfList' 31 1 2 4 [23, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [4], [8], [2, 8, 1]]]
 h' := ![![[0, 1], [1], [2], [16], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P31P4 : CertificateIrreducibleZModOfList' 31 1 2 4 [25, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [5], [1], [5, 6, 1]]]
 h' := ![![[0, 1], [30], [6], [30], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A31 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 31 5 where
 D := ![[4, 1], [19, 1], [22, 1], [23, 1], [25, 1]]; D' := ![[4, 1], [19, 1], [22, 1], [23, 1], [25, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4, 4, 4, 4, 4]
 n := ![1, 1, 1, 1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P31P0
  | 1 => exact P31P1
  | 2 => exact P31P2
  | 3 => exact P31P3
  | 4 => exact P31P4

def C310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A31.D 0) 31 where
  n := 1
  w := ![![31, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C311 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A31.D 1) 31 where
  n := 1
  w := ![![31, 0, 0, 0, 0], ![19, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C312 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A31.D 2) 31 where
  n := 1
  w := ![![31, 0, 0, 0, 0], ![22, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C313 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A31.D 3) 31 where
  n := 1
  w := ![![31, 0, 0, 0, 0], ![23, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C314 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A31.D 4) 31 where
  n := 1
  w := ![![31, 0, 0, 0, 0], ![25, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K31 : KummerData 31 ![I31N0, I31N1, I31N2, I31N3, I31N4] ![31, 31, 31, 31, 31] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A31
  C := by
    intro i
    match i with
    | 0 => exact C310
    | 1 => exact C311
    | 2 => exact C312
    | 3 => exact C313
    | 4 => exact C314
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 31 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![665, 2152, 10902, -2982, 22728]] i)))

def P37P0 : CertificateIrreducibleZModOfList' 37 1 2 5 [9, 1] where
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
 g := ![![[], [], [33], [], [28, 1]]]
 h' := ![![[0, 1], [1], [36], [12], [7], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P37P1 : CertificateIrreducibleZModOfList' 37 4 2 5 [17, 22, 7, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 25, 6, 7], [29, 13, 22, 10], [2, 35, 9, 20], [0, 1]]
 g := ![![[10, 32, 12, 30], [3, 4, 4], [21, 36, 11, 7], [1], []], ![[6, 7, 34, 17, 7, 10], [0, 33, 36], [14, 13, 12, 13, 12, 11], [7, 4, 16], [32, 7, 12]], ![[30, 30, 17, 31, 0, 11], [10, 21, 7], [29, 16, 28, 8, 32, 25], [25, 1, 11], [5, 8, 26]], ![[16, 35, 30, 8, 29, 14], [27, 13, 30], [15, 0, 17, 26, 29, 24], [34, 13, 28], [22, 1, 30]]]
 h' := ![![[15, 25, 6, 7], [7, 28, 12, 17], [13, 29, 29, 2], [20, 15, 30, 9], [0, 0, 1], [0, 1]], ![[29, 13, 22, 10], [27, 4, 29, 7], [8, 33, 22, 6], [3, 28, 27, 19], [14, 1, 1, 4], [15, 25, 6, 7]], ![[2, 35, 9, 20], [11, 29, 30, 29], [12, 16, 10, 9], [16, 1, 11, 13], [16, 27, 15, 14], [29, 13, 22, 10]], ![[0, 1], [32, 13, 3, 21], [26, 33, 13, 20], [14, 30, 6, 33], [0, 9, 20, 19], [2, 35, 9, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 14, 19], []]
 b := ![[], [], [15, 0, 11, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A37 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 37 2 where
 D := ![[9, 1], [17, 22, 7, 28, 1]]; D' := ![[9, 1], [17, 22, 7, 28, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5, 5]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P37P0
  | 1 => exact P37P1

def C370 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A37.D 0) 37 where
  n := 1
  w := ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A37.D 1) 37 where
  n := 4
  w := ![![37, 0, 0, 0, 0], ![665, 2152, 10902, -2982, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K37 : KummerData 37 ![I37N0, I37N1] ![37, 1874161] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![32, 1, 0, 0, 0]] i)))

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![39, 1, 0, 0, 0]] i)))

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![15, 22, 11, 2, 0]] i)))

def P41P0 : CertificateIrreducibleZModOfList' 41 1 2 5 [32, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [1], [9, 1]]]
 h' := ![![[0, 1], [1], [40], [9], [40], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P41P1 : CertificateIrreducibleZModOfList' 41 1 2 5 [39, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [16], [2, 1]]]
 h' := ![![[0, 1], [1], [40], [32], [4], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P41P2 : CertificateIrreducibleZModOfList' 41 3 2 5 [15, 21, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 39, 33], [8, 1, 8], [0, 1]]
 g := ![![[4, 29, 37], [], [2, 37], [18, 30, 1], []], ![[30, 20, 11, 40], [1, 37], [], [6, 8, 39, 33], [25, 23]], ![[3, 12, 0, 4], [2, 37], [1, 37], [8, 16, 33, 32], [9, 23]]]
 h' := ![![[22, 39, 33], [5, 38, 23], [13, 33], [17, 33, 18], [0, 0, 1], [0, 1]], ![[8, 1, 8], [27, 30, 6], [1, 16, 23], [40, 33], [27, 26, 1], [22, 39, 33]], ![[0, 1], [29, 14, 12], [31, 33, 18], [28, 16, 23], [11, 15, 39], [8, 1, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 25], []]
 b := ![[], [19, 5, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A41 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 41 3 where
 D := ![[32, 1], [39, 1], [15, 21, 11, 1]]; D' := ![[32, 1], [39, 1], [15, 21, 11, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5, 5, 5]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P41P0
  | 1 => exact P41P1
  | 2 => exact P41P2

def C410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A41.D 0) 41 where
  n := 1
  w := ![![41, 0, 0, 0, 0], ![32, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C411 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A41.D 1) 41 where
  n := 1
  w := ![![41, 0, 0, 0, 0], ![39, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C412 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A41.D 2) 41 where
  n := 3
  w := ![![41, 0, 0, 0, 0], ![15, 22, 11, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K41 : KummerData 41 ![I41N0, I41N1, I41N2] ![41, 41, 68921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A41
  C := by
    intro i
    match i with
    | 0 => exact C410
    | 1 => exact C411
    | 2 => exact C412
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 41 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] i)))

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![680, 2168, 10919, -2980, 22728]] i)))

def P43P0 : CertificateIrreducibleZModOfList' 43 1 2 5 [14, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [40], [], [17], [29, 1]]]
 h' := ![![[0, 1], [42], [13], [20], [24], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P43P1 : CertificateIrreducibleZModOfList' 43 4 2 5 [32, 37, 24, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 23, 17, 34], [13, 20, 23, 17], [7, 42, 3, 35], [0, 1]]
 g := ![![[19, 14, 15, 40], [6, 30, 14, 24], [24], [14, 1], []], ![[9, 36, 1, 0, 18, 27], [16, 37, 5, 14, 1, 33], [28, 30, 24], [40, 40, 1, 40, 23, 18], [20, 11, 38]], ![[14, 32, 41, 2, 29, 10], [32, 13, 34, 8, 36, 38], [26, 1, 16], [37, 9, 11, 16, 38, 11], [31, 12, 31]], ![[17, 38, 17, 4, 12, 13], [24, 11, 5, 2, 18, 36], [32, 28, 23], [28, 13, 39, 40, 12, 17], [41, 31, 21]]]
 h' := ![![[37, 23, 17, 34], [23, 3, 27, 13], [29, 35, 33, 29], [25, 9, 14], [0, 0, 1], [0, 1]], ![[13, 20, 23, 17], [0, 27, 29, 30], [31, 37, 15, 38], [29, 18, 29, 14], [41, 8, 28, 16], [37, 23, 17, 34]], ![[7, 42, 3, 35], [32, 36, 28, 37], [38, 25, 2, 38], [15, 1, 42, 4], [37, 21, 22, 17], [13, 20, 23, 17]], ![[0, 1], [2, 20, 2, 6], [14, 32, 36, 24], [36, 15, 1, 25], [27, 14, 35, 10], [7, 42, 3, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [41, 34, 12], []]
 b := ![[], [], [5, 4, 38, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A43 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 43 2 where
 D := ![[14, 1], [32, 37, 24, 29, 1]]; D' := ![[14, 1], [32, 37, 24, 29, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5, 5]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P43P0
  | 1 => exact P43P1

def C430 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A43.D 0) 43 where
  n := 1
  w := ![![43, 0, 0, 0, 0], ![14, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A43.D 1) 43 where
  n := 4
  w := ![![43, 0, 0, 0, 0], ![680, 2168, 10919, -2980, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K43 : KummerData 43 ![I43N0, I43N1] ![43, 3418801] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A43
  C := by
    intro i
    match i with
    | 0 => exact C430
    | 1 => exact C431
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 43 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![10, 2, 1, 0, 0]] i)))

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![26, 42, 45, 2, 0]] i)))

def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [10, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[19, 12], [38, 3], [37, 16], [32, 4], [1]], ![[42, 35], [32, 44], [5, 31], [24, 43], [1]]]
 h' := ![![[45, 46], [43, 24], [6, 35], [9, 43], [37, 45], [0, 1]], ![[0, 1], [42, 23], [30, 12], [17, 4], [41, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [34, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P47P1 : CertificateIrreducibleZModOfList' 47 3 2 5 [26, 41, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 41, 1], [34, 5, 46], [0, 1]]
 g := ![![[41, 29, 18], [17, 23, 14], [34, 27, 36], [10, 2, 1], []], ![[38, 4, 12, 9], [19, 12, 36, 4], [40, 5, 34, 34], [7, 44, 13, 25], [37, 1]], ![[19, 35, 36, 35], [13, 6, 37, 35], [16, 2, 34, 38], [44, 5, 10, 11], [39, 1]]]
 h' := ![![[15, 41, 1], [28, 8, 26], [9, 33, 22], [22, 8, 6], [0, 0, 1], [0, 1]], ![[34, 5, 46], [21, 39, 44], [35, 13, 2], [44, 1, 38], [15, 16, 5], [15, 41, 1]], ![[0, 1], [44, 0, 24], [25, 1, 23], [18, 38, 3], [1, 31, 41], [34, 5, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 25], []]
 b := ![[], [17, 33, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A47 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 47 2 where
 D := ![[10, 2, 1], [26, 41, 45, 1]]; D' := ![[10, 2, 1], [26, 41, 45, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5, 5]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P47P0
  | 1 => exact P47P1

def C470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A47.D 0) 47 where
  n := 2
  w := ![![47, 0, 0, 0, 0], ![10, 2, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A47.D 1) 47 where
  n := 3
  w := ![![47, 0, 0, 0, 0], ![26, 42, 45, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K47 : KummerData 47 ![I47N0, I47N1] ![2209, 103823] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A47
  C := by
    intro i
    match i with
    | 0 => exact C470
    | 1 => exact C471
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 47 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![35, 1, 0, 0, 0]] i)))

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![691, 2128, 10901, -3002, 22728]] i)))

def P53P0 : CertificateIrreducibleZModOfList' 53 1 2 5 [35, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [16], [], [6, 18, 1]]]
 h' := ![![[0, 1], [52], [23], [4], [2], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P53P1 : CertificateIrreducibleZModOfList' 53 4 2 5 [43, 8, 6, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 14, 41, 7], [15, 1, 20, 50], [24, 37, 45, 49], [0, 1]]
 g := ![![[42, 42, 25, 25], [50, 33, 28], [43, 45, 48, 36], [0, 35, 1], []], ![[27, 38, 7, 38, 13, 4], [17], [20, 29, 34, 32, 14, 15], [46, 25, 44], [19, 2, 20, 52, 12, 25]], ![[51, 51, 16, 44, 31, 22], [0, 32, 28], [33, 51, 17, 13, 46, 51], [28, 43, 40], [48, 38, 17, 10, 19, 26]], ![[15, 51, 15, 19, 36, 24], [17, 38, 6], [51, 27, 8, 28, 11, 52], [0, 24, 47], [46, 4, 1, 23, 26, 42]]]
 h' := ![![[49, 14, 41, 7], [6, 36, 21, 5], [6, 0, 21, 9], [0, 32, 48, 47], [0, 0, 0, 1], [0, 1]], ![[15, 1, 20, 50], [36, 24, 50, 29], [48, 37, 21], [12, 17, 12, 26], [20, 10, 4, 16], [49, 14, 41, 7]], ![[24, 37, 45, 49], [40, 43, 27, 9], [27, 41, 18, 9], [52, 21, 5, 6], [39, 35, 32, 26], [15, 1, 20, 50]], ![[0, 1], [22, 3, 8, 10], [8, 28, 46, 35], [40, 36, 41, 27], [27, 8, 17, 10], [24, 37, 45, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [39, 6, 2], []]
 b := ![[], [], [19, 15, 42, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A53 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 53 2 where
 D := ![[35, 1], [43, 8, 6, 18, 1]]; D' := ![[35, 1], [43, 8, 6, 18, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5, 5]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P53P0
  | 1 => exact P53P1

def C530 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A53.D 0) 53 where
  n := 1
  w := ![![53, 0, 0, 0, 0], ![35, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A53.D 1) 53 where
  n := 4
  w := ![![53, 0, 0, 0, 0], ![691, 2128, 10901, -3002, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K53 : KummerData 53 ![I53N0, I53N1] ![53, 7890481] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A53
  C := by
    intro i
    match i with
    | 0 => exact C530
    | 1 => exact C531
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 53 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![18, 1, 0, 0, 0]] i)))

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![49, 1, 0, 0, 0]] i)))

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![48, 9, 51, 2, 0]] i)))

def P59P0 : CertificateIrreducibleZModOfList' 59 1 2 5 [18, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [36], [], [22], [29, 41, 1]]]
 h' := ![![[0, 1], [1], [53], [17], [9], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P59P1 : CertificateIrreducibleZModOfList' 59 1 2 5 [49, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [53], [], [9], [41, 10, 1]]]
 h' := ![![[0, 1], [58], [17], [31], [56], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P59P2 : CertificateIrreducibleZModOfList' 59 3 2 5 [48, 8, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 18, 52], [20, 40, 7], [0, 1]]
 g := ![![[15, 24, 35], [28, 26, 27], [45, 21], [27, 30, 5], [1]], ![[36, 8, 17, 54], [2, 38, 19, 39], [26, 3], [54, 58, 37, 34], [56, 0, 20, 11]], ![[49, 42, 9, 3], [36, 37, 41, 36], [28, 28], [53, 0, 52, 46], [11, 10, 10, 48]]]
 h' := ![![[47, 18, 52], [13, 24, 34], [27, 44, 26], [2, 58, 32], [11, 51, 8], [0, 1]], ![[20, 40, 7], [46, 33, 12], [36, 1, 24], [35, 16, 48], [9, 12, 22], [47, 18, 52]], ![[0, 1], [34, 2, 13], [25, 14, 9], [22, 44, 38], [38, 55, 29], [20, 40, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 44], []]
 b := ![[], [1, 26, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A59 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 59 3 where
 D := ![[18, 1], [49, 1], [48, 8, 51, 1]]; D' := ![[18, 1], [49, 1], [48, 8, 51, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5, 5, 5]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P59P0
  | 1 => exact P59P1
  | 2 => exact P59P2

def C590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A59.D 0) 59 where
  n := 1
  w := ![![59, 0, 0, 0, 0], ![18, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C591 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A59.D 1) 59 where
  n := 1
  w := ![![59, 0, 0, 0, 0], ![49, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C592 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A59.D 2) 59 where
  n := 3
  w := ![![59, 0, 0, 0, 0], ![48, 9, 51, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K59 : KummerData 59 ![I59N0, I59N1, I59N2] ![59, 59, 205379] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A59
  C := by
    intro i
    match i with
    | 0 => exact C590
    | 1 => exact C591
    | 2 => exact C592
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 59 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![15738, 549, 122, 0, 0]] i)))

def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [18, 24, 22, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 22, 23, 1, 44], [19, 58, 9, 4, 37], [33, 14, 40, 42, 51], [5, 27, 50, 14, 51], [0, 1]]
 g := ![![[54, 59, 43, 24, 57], [28, 58, 48, 34], [2, 37, 26, 19, 57], [0, 0, 1], []], ![[13, 17, 10, 11, 19, 1, 29, 44], [13, 31, 45, 3], [11, 51, 32, 42, 15, 54, 59, 30], [10, 56, 42, 5, 3, 30, 5, 23], [40, 17, 30, 13, 9, 4, 13, 28]], ![[6, 19, 17, 31, 2, 11], [24, 27, 1, 14], [52, 1, 14, 3, 42, 51, 55, 50], [41, 57, 39, 47, 15, 54, 55, 55], [43, 30, 12, 8, 48, 4, 19, 23]], ![[52, 29, 21, 28, 26, 47, 25, 44], [55, 30, 56, 41], [37, 52, 9, 35, 43, 39, 59, 43], [17, 14, 40, 35, 31, 22, 41, 11], [44, 3, 7, 24, 37, 11, 34, 37]], ![[59, 47, 53, 38, 60, 58, 45, 8], [44, 20, 28, 5], [24, 21, 46, 32, 21, 47, 3, 6], [7, 26, 59, 60, 23, 16, 51, 37], [45, 36, 18, 57, 55, 31, 52, 37]]]
 h' := ![![[4, 22, 23, 1, 44], [60, 38, 42, 56, 22], [25, 18, 3, 50, 20], [0, 0, 43, 37, 39], [0, 0, 0, 1], [0, 1]], ![[19, 58, 9, 4, 37], [32, 9, 22, 53, 1], [12, 29, 40, 60, 8], [49, 35, 48, 33, 3], [15, 34, 21, 40, 14], [4, 22, 23, 1, 44]], ![[33, 14, 40, 42, 51], [60, 59, 56, 27], [59, 40, 57, 16, 21], [60, 41, 33, 60, 53], [46, 59, 21, 13, 31], [19, 58, 9, 4, 37]], ![[5, 27, 50, 14, 51], [48, 5, 5, 13, 9], [60, 13, 16, 20, 38], [49, 4, 41, 29, 21], [9, 37, 17, 11, 26], [33, 14, 40, 42, 51]], ![[0, 1], [26, 11, 58, 34, 29], [56, 22, 6, 37, 35], [0, 42, 18, 24, 6], [47, 53, 2, 57, 51], [5, 27, 50, 14, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 22, 49, 30], [], [], []]
 b := ![[], [55, 36, 53, 49, 52], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A61 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 61 1 where
 D := ![[18, 24, 22, 0, 0, 1]]; D' := ![[18, 24, 22, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P61P0

def C610 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A61.D 0) 61 where
  n := 5
  w := ![![61, 0, 0, 0, 0], ![15738, 549, 122, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K61 : KummerData 61 ![I61N0] ![844596301] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A61
  C := by
    intro i
    match i with
    | 0 => exact C610
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 61 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)
  decide

def PB18792I1 : PrimesBelowBoundCertificateInterval O 23 61 18792 where
  m := 9
  g := ![1, 5, 2, 3, 2, 2, 2, 3, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB18792I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2, I31N3, I31N4]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K29) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K31) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K37) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K41) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K43) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K47) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K53) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K59) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K61) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20511149]
    · exact ![31, 31, 31, 31, 31]
    · exact ![37, 1874161]
    · exact ![41, 41, 68921]
    · exact ![43, 3418801]
    · exact ![2209, 103823]
    · exact ![53, 7890481]
    · exact ![59, 59, 205379]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K29)
    · exact (card_quot_of_KummerData K31)
    · exact (card_quot_of_KummerData K37)
    · exact (card_quot_of_KummerData K41)
    · exact (card_quot_of_KummerData K43)
    · exact (card_quot_of_KummerData K47)
    · exact (card_quot_of_KummerData K53)
    · exact (card_quot_of_KummerData K59)
    · exact (card_quot_of_KummerData K61)
  β := ![I31N0, I31N1, I31N2, I31N3, I31N4, I37N0, I41N0, I41N1, I43N0, I47N0, I53N0, I59N0, I59N1]
  Il := ![[], [I31N0, I31N1, I31N2, I31N3, I31N4], [I37N0], [I41N0, I41N1], [I43N0], [I47N0], [I53N0], [I59N0, I59N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
