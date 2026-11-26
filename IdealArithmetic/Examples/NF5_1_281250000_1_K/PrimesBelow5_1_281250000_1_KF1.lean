
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![17, 10, 1, 0, 0]] i)))

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![9, 13, 1, 0, 0]] i)))

def P29P0 : CertificateIrreducibleZModOfList' 29 1 2 4 [6, 1] where
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
 g := ![![[], [], [24], [7, 23, 1]]]
 h' := ![![[0, 1], [1], [1], [16], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [17, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 28], [0, 1]]
 g := ![![[4, 23], [23], [17, 16], [19, 1]], ![[6, 6], [23], [2, 13], [9, 28]]]
 h' := ![![[19, 28], [16, 20], [1, 9], [25, 25], [0, 1]], ![[0, 1], [19, 9], [27, 20], [7, 4], [19, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [16, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P29P2 : CertificateIrreducibleZModOfList' 29 2 2 4 [9, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 28], [0, 1]]
 g := ![![[24, 13], [1], [5, 22], [16, 1]], ![[0, 16], [1], [9, 7], [3, 28]]]
 h' := ![![[16, 28], [15, 19], [13, 28], [1, 15], [0, 1]], ![[0, 1], [0, 10], [26, 1], [9, 14], [16, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [18, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A29 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 29 3 where
 D := ![[6, 1], [17, 10, 1], [9, 13, 1]]; D' := ![[6, 1], [17, 10, 1], [9, 13, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4, 4, 4]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P29P0
  | 1 => exact P29P1
  | 2 => exact P29P2

def C290 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A29.D 0) 29 where
  n := 1
  w := ![![29, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C291 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A29.D 1) 29 where
  n := 2
  w := ![![29, 0, 0, 0, 0], ![17, 10, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C292 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A29.D 2) 29 where
  n := 2
  w := ![![29, 0, 0, 0, 0], ![9, 13, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K29 : KummerData 29 ![I29N0, I29N1, I29N2] ![29, 841, 841] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A29
  C := by
    intro i
    match i with
    | 0 => exact C290
    | 1 => exact C291
    | 2 => exact C292
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 29 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] i)))

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0]] i)))

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![15, 27, 30, 5, 0]] i)))

def P31P0 : CertificateIrreducibleZModOfList' 31 1 2 4 [5, 1] where
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
 g := ![![[], [25], [1], [25, 26, 1]]]
 h' := ![![[0, 1], [30], [26], [30], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P31P1 : CertificateIrreducibleZModOfList' 31 1 2 4 [27, 1] where
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
 g := ![![[], [8], [4], [16, 4, 1]]]
 h' := ![![[0, 1], [1], [16], [2], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P31P2 : CertificateIrreducibleZModOfList' 31 3 2 4 [15, 27, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 7, 24], [13, 23, 7], [0, 1]]
 g := ![![[7, 12, 28], [27, 23, 18], [30, 9, 1], [1]], ![[1, 27, 2, 12], [21, 25, 14, 15], [26, 2, 19, 11], [4, 24, 4, 29]], ![[25, 2, 3, 2], [12, 1, 1, 20], [18, 21, 30, 19], [16, 12, 4, 2]]]
 h' := ![![[19, 7, 24], [29, 19, 11], [15, 24, 24], [16, 4, 1], [0, 1]], ![[13, 23, 7], [15, 10, 27], [22, 18, 12], [10, 14, 26], [19, 7, 24]], ![[0, 1], [6, 2, 24], [0, 20, 26], [4, 13, 4], [13, 23, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 24], []]
 b := ![[], [14, 5, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A31 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 31 3 where
 D := ![[5, 1], [27, 1], [15, 27, 30, 1]]; D' := ![[5, 1], [27, 1], [15, 27, 30, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4, 4, 4]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P31P0
  | 1 => exact P31P1
  | 2 => exact P31P2

def C310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A31.D 0) 31 where
  n := 1
  w := ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C311 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A31.D 1) 31 where
  n := 1
  w := ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C312 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A31.D 2) 31 where
  n := 3
  w := ![![31, 0, 0, 0, 0], ![15, 27, 30, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K31 : KummerData 31 ![I31N0, I31N1, I31N2] ![31, 31, 29791] where
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
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 31 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![36, 1, 0, 0, 0]] i)))

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![4, 13, 18, 5, 10]] i)))

def P37P0 : CertificateIrreducibleZModOfList' 37 1 2 5 [36, 1] where
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
 g := ![![[], [], [1], [], [1, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P37P1 : CertificateIrreducibleZModOfList' 37 4 2 5 [4, 13, 13, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 22, 28, 35], [24, 11, 17, 31], [8, 3, 29, 8], [0, 1]]
 g := ![![[36, 10, 30, 21], [30, 6, 21], [36, 9, 25, 1], [1], []], ![[15, 35, 4, 15, 1, 17], [32, 26, 16], [31, 32, 6, 16, 14, 35], [4, 27, 33], [20, 32, 4]], ![[21, 35, 0, 20, 30, 17], [2, 17, 16], [2, 10, 24, 27, 20, 2], [22, 20, 9], [3, 19, 36]], ![[15, 15, 10, 10, 27, 29], [0, 26, 21], [26, 14, 35, 10, 29, 15], [33, 2, 3], [27, 30, 27]]]
 h' := ![![[4, 22, 28, 35], [7, 11, 29, 13], [4, 30, 11, 13], [33, 24, 24, 36], [0, 0, 1], [0, 1]], ![[24, 11, 17, 31], [13, 6, 11, 11], [17, 22, 33, 4], [10, 3, 33, 36], [10, 10, 16, 25], [4, 22, 28, 35]], ![[8, 3, 29, 8], [26, 36, 16, 19], [21, 26, 19, 33], [30, 1, 33, 7], [9, 6, 26, 34], [24, 11, 17, 31]], ![[0, 1], [10, 21, 18, 31], [26, 33, 11, 24], [28, 9, 21, 32], [30, 21, 31, 15], [8, 3, 29, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 27, 5], []]
 b := ![[], [], [21, 9, 19, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A37 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 37 2 where
 D := ![[36, 1], [4, 13, 13, 1, 1]]; D' := ![[36, 1], [4, 13, 13, 1, 1]]
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
  w := ![![37, 0, 0, 0, 0], ![36, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A37.D 1) 37 where
  n := 4
  w := ![![37, 0, 0, 0, 0], ![4, 13, 18, 5, 10]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![18, 1, 0, 0, 0]] i)))

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![20, 1, 0, 0, 0]] i)))

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![6, 34, 3, 5, 0]] i)))

def P41P0 : CertificateIrreducibleZModOfList' 41 1 2 5 [18, 1] where
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
 g := ![![[], [], [], [16], [23, 1]]]
 h' := ![![[0, 1], [1], [1], [40], [37], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P41P1 : CertificateIrreducibleZModOfList' 41 1 2 5 [20, 1] where
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
 g := ![![[], [], [], [18], [21, 1]]]
 h' := ![![[0, 1], [1], [40], [9], [31], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P41P2 : CertificateIrreducibleZModOfList' 41 3 2 5 [6, 34, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 16, 28], [19, 24, 13], [0, 1]]
 g := ![![[31], [1, 20], [33, 8], [16, 38, 1], []], ![[40, 26, 37, 35], [39, 16], [0, 25], [31, 37, 3, 15], [20, 5]], ![[9, 40, 31, 6], [24, 39], [27, 4], [18, 24, 11, 7], [35, 5]]]
 h' := ![![[19, 16, 28], [39, 21], [39, 28, 15], [27, 7, 7], [0, 0, 1], [0, 1]], ![[19, 24, 13], [28, 8, 14], [4, 25, 37], [2, 13, 36], [36, 21, 24], [19, 16, 28]], ![[0, 1], [28, 12, 27], [7, 29, 30], [28, 21, 39], [28, 20, 16], [19, 24, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 21], []]
 b := ![[], [24, 31, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A41 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 41 3 where
 D := ![[18, 1], [20, 1], [6, 34, 3, 1]]; D' := ![[18, 1], [20, 1], [6, 34, 3, 1]]
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
  w := ![![41, 0, 0, 0, 0], ![18, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C411 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A41.D 1) 41 where
  n := 1
  w := ![![41, 0, 0, 0, 0], ![20, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C412 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A41.D 2) 41 where
  n := 3
  w := ![![41, 0, 0, 0, 0], ![6, 34, 3, 5, 0]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![30, 1, 0, 0, 0]] i)))

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![33, 23, 20, 65, 10]] i)))

def P43P0 : CertificateIrreducibleZModOfList' 43 1 2 5 [30, 1] where
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
 g := ![![[], [10], [], [9], [13, 1]]]
 h' := ![![[0, 1], [1], [15], [31], [40], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P43P1 : CertificateIrreducibleZModOfList' 43 4 2 5 [33, 23, 15, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 32, 5, 8], [12, 42, 13, 8], [40, 11, 25, 27], [0, 1]]
 g := ![![[15, 1, 19, 36], [19, 7, 8, 9], [29, 2, 23], [30, 1], []], ![[32, 21, 11, 18, 37, 19], [11, 36, 2, 25, 25, 18], [12, 25, 21], [4, 32, 22, 19, 38, 19], [22, 22, 21]], ![[20, 0, 32, 42, 33, 33], [8, 15, 34, 3, 15, 12], [25, 31, 41], [12, 16, 36, 3, 10, 39], [38, 21, 21]], ![[26, 0, 6, 10, 18, 34], [11, 41, 34, 32, 33, 22], [28, 22, 1], [14, 0, 27, 22, 9, 39], [2, 0, 41]]]
 h' := ![![[21, 32, 5, 8], [18, 34, 37, 6], [33, 25, 28, 3], [42, 8, 0, 25], [0, 0, 1], [0, 1]], ![[12, 42, 13, 8], [33, 12, 12, 30], [38, 36, 17, 20], [41, 6, 19, 35], [16, 26, 6, 30], [21, 32, 5, 8]], ![[40, 11, 25, 27], [42, 9, 38, 17], [2, 18, 33, 18], [28, 35, 20, 27], [8, 0, 29, 35], [12, 42, 13, 8]], ![[0, 1], [12, 31, 42, 33], [2, 7, 8, 2], [25, 37, 4, 42], [29, 17, 7, 21], [40, 11, 25, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 41, 24], []]
 b := ![[], [], [6, 4, 36, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A43 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 43 2 where
 D := ![[30, 1], [33, 23, 15, 13, 1]]; D' := ![[30, 1], [33, 23, 15, 13, 1]]
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
  w := ![![43, 0, 0, 0, 0], ![30, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A43.D 1) 43 where
  n := 4
  w := ![![43, 0, 0, 0, 0], ![33, 23, 20, 65, 10]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![19, 1, 0, 0, 0]] i)))

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![34, 1, 0, 0, 0]] i)))

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![40, 1, 0, 0, 0]] i)))

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![30, 1, 1, 0, 0]] i)))

def P47P0 : CertificateIrreducibleZModOfList' 47 1 2 5 [19, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [42], [4], [37], [28, 1]]]
 h' := ![![[0, 1], [1], [18], [2], [32], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P47P1 : CertificateIrreducibleZModOfList' 47 1 2 5 [34, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [18], [2], [32], [13, 1]]]
 h' := ![![[0, 1], [46], [26], [40], [28], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P47P2 : CertificateIrreducibleZModOfList' 47 1 2 5 [40, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [27], [32], [4], [7, 1]]]
 h' := ![![[0, 1], [1], [36], [28], [2], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P47P3 : CertificateIrreducibleZModOfList' 47 2 2 5 [30, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 46], [0, 1]]
 g := ![![[11, 24], [39, 24], [5, 3], [12, 1], [1]], ![[34, 23], [15, 23], [2, 44], [11, 46], [1]]]
 h' := ![![[46, 46], [5, 27], [38, 20], [16, 12], [17, 46], [0, 1]], ![[0, 1], [25, 20], [18, 27], [4, 35], [18, 1], [46, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [32, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A47 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 47 4 where
 D := ![[19, 1], [34, 1], [40, 1], [30, 1, 1]]; D' := ![[19, 1], [34, 1], [40, 1], [30, 1, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5, 5, 5, 5]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P47P0
  | 1 => exact P47P1
  | 2 => exact P47P2
  | 3 => exact P47P3

def C470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A47.D 0) 47 where
  n := 1
  w := ![![47, 0, 0, 0, 0], ![19, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A47.D 1) 47 where
  n := 1
  w := ![![47, 0, 0, 0, 0], ![34, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C472 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A47.D 2) 47 where
  n := 1
  w := ![![47, 0, 0, 0, 0], ![40, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C473 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A47.D 3) 47 where
  n := 2
  w := ![![47, 0, 0, 0, 0], ![30, 1, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K47 : KummerData 47 ![I47N0, I47N1, I47N2, I47N3] ![47, 47, 47, 2209] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A47
  C := by
    intro i
    match i with
    | 0 => exact C470
    | 1 => exact C471
    | 2 => exact C472
    | 3 => exact C473
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 47 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] i)))

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![48, 44, 29, 230, 10]] i)))

def P53P0 : CertificateIrreducibleZModOfList' 53 1 2 5 [7, 1] where
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
 g := ![![[], [], [15], [], [49, 46, 1]]]
 h' := ![![[0, 1], [1], [1], [42], [28], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P53P1 : CertificateIrreducibleZModOfList' 53 4 2 5 [48, 44, 24, 46, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 0, 18, 15], [10, 14, 26, 34], [14, 38, 9, 4], [0, 1]]
 g := ![![[39, 2, 5, 46], [15, 34, 17], [18, 19, 32, 44], [25, 7, 1], []], ![[52, 50, 31, 40, 2, 7], [36, 27, 37], [33, 14, 19, 50, 16, 25], [47, 36, 37], [19, 4, 10, 42, 0, 36]], ![[19, 20, 24, 48, 20, 51], [19, 6, 40], [38, 30, 41, 12, 28, 45], [40, 6, 4], [50, 4, 45, 35, 20, 31]], ![[7, 51, 34, 51, 40, 24], [49, 15, 28], [13, 42, 45, 6, 5, 10], [30, 47, 15], [32, 24, 36, 0, 32, 11]]]
 h' := ![![[36, 0, 18, 15], [13, 33, 21, 24], [37, 35, 27, 21], [19, 48, 51, 16], [0, 0, 0, 1], [0, 1]], ![[10, 14, 26, 34], [46, 30, 36, 2], [5, 26, 22, 14], [48, 22, 19, 39], [5, 32, 25, 39], [36, 0, 18, 15]], ![[14, 38, 9, 4], [33, 33, 51, 9], [16, 8, 44, 27], [48, 20, 28, 18], [31, 6, 21, 2], [10, 14, 26, 34]], ![[0, 1], [17, 10, 51, 18], [39, 37, 13, 44], [6, 16, 8, 33], [42, 15, 7, 11], [14, 38, 9, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 22, 9], []]
 b := ![[], [], [19, 50, 28, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A53 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 53 2 where
 D := ![[7, 1], [48, 44, 24, 46, 1]]; D' := ![[7, 1], [48, 44, 24, 46, 1]]
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
  w := ![![53, 0, 0, 0, 0], ![7, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A53.D 1) 53 where
  n := 4
  w := ![![53, 0, 0, 0, 0], ![48, 44, 29, 230, 10]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![354, -236, 0, 295, 0]] i)))

def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [54, 14, 0, 34, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 58, 30, 9, 53], [10, 10, 28, 54, 6], [5, 42, 44, 19, 56], [44, 7, 16, 36, 3], [0, 1]]
 g := ![![[0, 31, 40, 54, 9], [30, 19, 36, 18, 5], [33, 28], [25, 0, 1], []], ![[2, 48, 46, 21, 29, 53, 43, 48], [58, 49, 23, 41, 29, 4, 14, 29], [49, 22, 26, 17], [35, 27, 34, 47, 38, 44, 19, 46], [9, 41, 12, 40, 38, 40, 28, 20]], ![[49, 32, 16, 47, 38, 29, 32, 52], [51, 13, 29, 50, 38, 17, 43, 42], [57, 51, 49, 20], [23, 2, 25, 53, 48, 23, 42, 13], [4, 35, 53, 29, 56, 24, 50, 39]], ![[36, 45, 51, 48, 38, 45, 45, 52], [28, 53, 15, 5, 0, 1, 14, 50], [34, 40, 49, 15], [36, 8, 34, 28, 28, 9, 47, 55], [43, 8, 26, 15, 47, 37, 41, 32]], ![[12, 50, 14, 33, 25, 57, 49, 15], [14, 45, 50, 23, 3, 4, 33, 17], [44, 37, 2, 19], [58, 48, 58, 9, 26, 30, 49, 4], [40, 4, 22, 28, 34, 27, 28, 27]]]
 h' := ![![[0, 58, 30, 9, 53], [32, 41, 54, 9, 3], [37, 29, 48, 38, 8], [7, 4, 5, 21], [0, 0, 0, 1], [0, 1]], ![[10, 10, 28, 54, 6], [54, 31, 49, 42, 13], [13, 35, 15, 12, 8], [57, 39, 37, 11, 28], [45, 20, 17, 20, 37], [0, 58, 30, 9, 53]], ![[5, 42, 44, 19, 56], [25, 12, 9, 47, 44], [6, 3, 2, 5, 19], [55, 35, 50, 55, 16], [17, 51, 24, 50, 22], [10, 10, 28, 54, 6]], ![[44, 7, 16, 36, 3], [16, 43, 33, 51, 50], [39, 33, 13, 36, 48], [39, 38, 22, 10, 29], [45, 51, 42, 51, 32], [5, 42, 44, 19, 56]], ![[0, 1], [2, 50, 32, 28, 8], [6, 18, 40, 27, 35], [9, 2, 4, 21, 45], [11, 55, 35, 55, 27], [44, 7, 16, 36, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 47, 4, 32], [], [], []]
 b := ![[], [5, 40, 42, 48, 25], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A59 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 59 1 where
 D := ![[54, 14, 0, 34, 0, 1]]; D' := ![[54, 14, 0, 34, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![5]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P59P0

def C590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A59.D 0) 59 where
  n := 5
  w := ![![59, 0, 0, 0, 0], ![354, -236, 0, 295, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K59 : KummerData 59 ![I59N0] ![714924299] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A59
  C := by
    intro i
    match i with
    | 0 => exact C590
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 59 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![305, -244, 0, 305, 0]] i)))

def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [5, 6, 0, 36, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 47, 44, 20, 42], [42, 36, 13, 4, 60], [11, 41, 44, 56, 41], [47, 58, 21, 42, 40], [0, 1]]
 g := ![![[20, 3, 31, 22, 56], [60, 20, 22, 60], [21, 32, 20], [25, 0, 1], []], ![[38, 10, 30, 17, 29, 9, 33, 15], [50, 25, 6, 45], [20, 23, 53, 25, 55, 10, 5, 4], [0, 44, 13, 4, 32, 29, 6, 27], [42, 10, 44, 40, 3, 21, 5, 34]], ![[24, 2, 48, 39, 16, 47, 17, 3], [9, 1, 33, 4], [59, 44, 39, 3, 52, 44, 55, 27], [50, 41, 15, 26, 16, 29, 57, 46], [37, 43, 30, 60, 38, 27, 12, 60]], ![[58, 50, 31, 49, 4, 3, 60, 16], [52, 9, 41, 14], [37, 29, 17, 38, 15, 43, 10, 48], [7, 53, 10, 55, 52, 24, 2, 34], [56, 30, 34, 47, 17, 18, 39, 52]], ![[52, 58, 18, 48, 7, 12, 36, 51], [55, 11, 38, 25], [25, 29, 44, 43, 59, 44], [0, 32, 38, 41, 57, 44, 24, 23], [23, 32, 6, 12, 37, 8, 56, 11]]]
 h' := ![![[22, 47, 44, 20, 42], [50, 4, 59, 7, 19], [17, 28, 59, 60, 50], [58, 33, 56, 9], [0, 0, 0, 1], [0, 1]], ![[42, 36, 13, 4, 60], [35, 50, 15, 30, 22], [38, 52, 32, 7, 44], [41, 34, 55, 55, 53], [7, 49, 50, 43, 35], [22, 47, 44, 20, 42]], ![[11, 41, 44, 56, 41], [12, 29, 35, 39, 27], [22, 2, 24, 54, 2], [58, 60, 17, 31, 20], [32, 60, 6, 33, 25], [42, 36, 13, 4, 60]], ![[47, 58, 21, 42, 40], [40, 36, 10, 5, 29], [19, 28, 33, 46, 21], [47, 46, 50, 46, 49], [14, 1, 30, 44, 23], [11, 41, 44, 56, 41]], ![[0, 1], [5, 3, 3, 41, 25], [6, 12, 35, 16, 5], [19, 10, 5, 42], [8, 12, 36, 1, 39], [47, 58, 21, 42, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 53, 43, 38], [], [], []]
 b := ![[], [15, 25, 46, 14, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A61 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 61 1 where
 D := ![[5, 6, 0, 36, 0, 1]]; D' := ![[5, 6, 0, 36, 0, 1]]
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
  w := ![![61, 0, 0, 0, 0], ![305, -244, 0, 305, 0]]
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


lemma PB1045I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)
  decide

def PB1045I1 : PrimesBelowBoundCertificateInterval O 23 61 1045 where
  m := 9
  g := ![3, 3, 2, 3, 2, 4, 2, 1, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1045I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2, I47N3]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![29, 841, 841]
    · exact ![31, 31, 29791]
    · exact ![37, 1874161]
    · exact ![41, 41, 68921]
    · exact ![43, 3418801]
    · exact ![47, 47, 47, 2209]
    · exact ![53, 7890481]
    · exact ![714924299]
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
  β := ![I29N0, I29N1, I29N2, I31N0, I31N1, I37N0, I41N0, I41N1, I43N0, I47N0, I47N1, I47N2, I53N0]
  Il := ![[I29N0, I29N1, I29N2], [I31N0, I31N1], [I37N0], [I41N0, I41N1], [I43N0], [I47N0, I47N1, I47N2], [I53N0], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
