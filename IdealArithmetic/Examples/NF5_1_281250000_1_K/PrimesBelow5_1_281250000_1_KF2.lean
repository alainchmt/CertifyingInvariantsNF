
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![43, 1, 0, 0, 0]] i)))

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![46, 25, 20, 120, 10]] i)))

def P67P0 : CertificateIrreducibleZModOfList' 67 1 2 6 [43, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [14], [], [], [], [24, 1]]]
 h' := ![![[0, 1], [1], [9], [64], [59], [40], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P67P1 : CertificateIrreducibleZModOfList' 67 4 2 6 [46, 25, 15, 24, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 54, 43, 60], [54, 11, 1, 42], [18, 1, 23, 32], [0, 1]]
 g := ![![[5, 14], [24, 30, 41, 19], [4, 27, 33], [19, 28, 40], [1], []], ![[16, 31, 18, 27, 21, 22], [47, 36, 14, 53, 64, 25], [55, 62, 25], [39, 17, 24], [51, 39, 47], [16, 31, 49]], ![[38, 54, 37, 0, 32, 41], [30, 5, 54, 53], [46, 38, 29], [14, 27, 36], [64, 57, 1], [62, 25, 22]], ![[33, 55, 55, 2, 16, 12], [3, 15, 38, 16, 11, 13], [50, 62, 22], [21, 1, 24], [43, 7, 37], [44, 11, 19]]]
 h' := ![![[38, 54, 43, 60], [35, 22, 58], [40, 3, 13, 32], [36, 1, 51, 10], [21, 42, 52, 43], [0, 0, 1], [0, 1]], ![[54, 11, 1, 42], [60, 49, 37, 63], [53, 42, 14, 41], [38, 50, 41, 62], [36, 13, 22, 15], [38, 0, 34, 28], [38, 54, 43, 60]], ![[18, 1, 23, 32], [44, 48, 26, 44], [64, 54, 42], [61, 22, 57, 37], [13, 26, 43, 61], [64, 29, 7, 1], [54, 11, 1, 42]], ![[0, 1], [53, 15, 13, 27], [27, 35, 65, 61], [7, 61, 52, 25], [54, 53, 17, 15], [42, 38, 25, 38], [18, 1, 23, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 56, 56], []]
 b := ![[], [], [30, 34, 22, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A67 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 67 2 where
 D := ![[43, 1], [46, 25, 15, 24, 1]]; D' := ![[43, 1], [46, 25, 15, 24, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P67P0
  | 1 => exact P67P1

def C670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A67.D 0) 67 where
  n := 1
  w := ![![67, 0, 0, 0, 0], ![43, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A67.D 1) 67 where
  n := 4
  w := ![![67, 0, 0, 0, 0], ![46, 25, 20, 120, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K67 : KummerData 67 ![I67N0, I67N1] ![67, 20151121] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A67
  C := by
    intro i
    match i with
    | 0 => exact C670
    | 1 => exact C671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 67 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![355, -213, 0, 355, 0]] i)))

def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [55, 37, 0, 46, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 45, 53, 62, 50], [36, 49, 61, 36, 24], [45, 67, 29, 32, 43], [38, 51, 70, 12, 25], [0, 1]]
 g := ![![[68, 39, 3, 54, 60], [11, 34, 70, 70, 50], [70, 57, 23, 1, 45], [0, 25, 0, 1], [], []], ![[28, 57, 36, 28, 11, 37, 23, 6], [29, 10, 24, 17, 59, 22, 43, 29], [69, 25, 53, 3, 6, 38, 34, 19], [12, 51, 2, 24], [70, 47, 14, 18], [3, 5, 23, 15]], ![[17, 49, 19, 9, 21, 24, 54, 5], [25, 59, 3, 44, 56, 67, 44, 1], [39, 34, 11, 33, 47, 61, 54, 6], [56, 39, 21, 43], [23, 7, 59, 1], [31, 22, 24, 8]], ![[64, 57, 7, 48, 17, 0, 66, 16], [42, 61, 45, 15, 3, 14, 24, 16], [31, 39, 28, 56, 22, 34, 44, 8], [49, 27, 18, 8], [30, 20, 40, 32], [22, 43, 54, 3]], ![[39, 46, 56, 68, 18, 18, 53, 43], [34, 26, 42, 57, 30, 52, 59, 2], [69, 44, 24, 17, 14, 16, 27, 1], [25, 12, 58, 36], [4, 22, 64, 2], [60, 28, 32, 57]]]
 h' := ![![[23, 45, 53, 62, 50], [34, 38, 24, 26, 42], [55, 26, 34, 29, 11], [0, 45, 69, 16, 20], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[36, 49, 61, 36, 24], [60, 2, 18, 52, 37], [31, 45, 52, 29, 59], [15, 52, 10, 56, 67], [65, 3, 11, 28, 33], [9, 51, 31, 57, 35], [23, 45, 53, 62, 50]], ![[45, 67, 29, 32, 43], [55, 44, 63, 16, 21], [34, 45, 15, 27, 28], [13, 20, 14, 7, 35], [18, 25, 69, 6, 55], [17, 35, 44, 65, 1], [36, 49, 61, 36, 24]], ![[38, 51, 70, 12, 25], [58, 59, 66, 35, 53], [18, 37, 24, 39, 18], [12, 0, 12, 47, 34], [3, 29, 4, 44, 47], [34, 11, 53, 41, 23], [45, 67, 29, 32, 43]], ![[0, 1], [19, 70, 42, 13, 60], [43, 60, 17, 18, 26], [32, 25, 37, 16, 57], [22, 14, 58, 64, 6], [61, 45, 13, 50, 12], [38, 51, 70, 12, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 61, 41, 66], [], [], []]
 b := ![[], [31, 52, 62, 32, 64], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A71 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 71 1 where
 D := ![[55, 37, 0, 46, 0, 1]]; D' := ![[55, 37, 0, 46, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P71P0

def C710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A71.D 0) 71 where
  n := 5
  w := ![![71, 0, 0, 0, 0], ![355, -213, 0, 355, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K71 : KummerData 71 ![I71N0] ![1804229351] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A71
  C := by
    intro i
    match i with
    | 0 => exact C710
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 71 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0], ![57, 1, 0, 0, 0]] i)))

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0], ![37, 46, 17, 80, 10]] i)))

def P73P0 : CertificateIrreducibleZModOfList' 73 1 2 6 [57, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [32], [], [16, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [55], [37], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P73P1 : CertificateIrreducibleZModOfList' 73 4 2 6 [37, 46, 12, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 58, 6, 66], [5, 34, 50, 36], [40, 53, 17, 44], [0, 1]]
 g := ![![[49, 64, 30, 1], [53, 1, 16], [72, 65, 16], [67, 47, 11, 37], [1], []], ![[71, 30, 13, 29, 4, 33], [40, 33, 1], [69, 28, 35], [19, 65, 61, 66, 16, 43], [60, 0, 16], [41, 8, 49]], ![[46, 31, 3, 55, 3, 18], [26, 22, 50], [66, 2, 27], [37, 22, 39, 0, 19, 27], [61, 22, 57], [42, 19, 55]], ![[33, 44, 50, 46, 48, 28], [24, 36, 48], [52, 63, 36], [5, 22, 15, 10, 4, 60], [35, 43, 12], [71, 12, 38]]]
 h' := ![![[12, 58, 6, 66], [9, 23, 50, 72], [46, 70, 50, 69], [3, 52, 31, 4], [36, 27, 61, 57], [0, 0, 1], [0, 1]], ![[5, 34, 50, 36], [7, 58, 62, 57], [10, 72, 61, 1], [9, 27, 51, 53], [20, 13, 45, 51], [14, 13, 32, 4], [12, 58, 6, 66]], ![[40, 53, 17, 44], [12, 72, 44, 57], [5, 33, 45, 14], [29, 63, 29, 10], [22, 66, 51, 47], [4, 41, 68, 38], [5, 34, 50, 36]], ![[0, 1], [6, 66, 63, 33], [50, 44, 63, 62], [21, 4, 35, 6], [44, 40, 62, 64], [68, 19, 45, 31], [40, 53, 17, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [58, 46, 14], []]
 b := ![[], [], [9, 1, 55, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A73 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 73 2 where
 D := ![[57, 1], [37, 46, 12, 16, 1]]; D' := ![[57, 1], [37, 46, 12, 16, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P73P0
  | 1 => exact P73P1

def C730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A73.D 0) 73 where
  n := 1
  w := ![![73, 0, 0, 0, 0], ![57, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A73.D 1) 73 where
  n := 4
  w := ![![73, 0, 0, 0, 0], ![37, 46, 17, 80, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K73 : KummerData 73 ![I73N0, I73N1] ![73, 28398241] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A73
  C := by
    intro i
    match i with
    | 0 => exact C730
    | 1 => exact C731
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 73 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![66, 1, 0, 0, 0]] i)))

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![48, 43, 11, 5, 0]] i)))

def P79P0 : CertificateIrreducibleZModOfList' 79 1 2 6 [2, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [40], [22], [19], [], [77, 1]]]
 h' := ![![[0, 1], [78], [35], [41], [16], [4], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P79P1 : CertificateIrreducibleZModOfList' 79 1 2 6 [66, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [73], [10], [26], [], [13, 1]]]
 h' := ![![[0, 1], [1], [51], [22], [42], [11], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P79P2 : CertificateIrreducibleZModOfList' 79 3 2 6 [48, 43, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 17, 65], [4, 61, 14], [0, 1]]
 g := ![![[25, 30, 76], [23, 13, 38], [38, 31, 1], [29, 8, 1], [68, 1], []], ![[45, 28, 47, 22], [50, 14, 46, 1], [48, 23, 33, 13], [70, 59, 77, 25], [48, 8], [54, 38]], ![[74, 7, 39, 61], [56, 3, 62, 77], [2, 43, 24, 34], [15, 25, 55, 27], [48, 52], [26, 38]]]
 h' := ![![[64, 17, 65], [2, 16, 32], [72, 69, 14], [30, 21, 1], [54, 30, 78], [0, 0, 1], [0, 1]], ![[4, 61, 14], [16, 37, 69], [27, 58, 46], [34, 46, 4], [75, 31, 72], [3, 5, 61], [64, 17, 65]], ![[0, 1], [63, 26, 57], [6, 31, 19], [67, 12, 74], [63, 18, 8], [32, 74, 17], [4, 61, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 13], []]
 b := ![[], [57, 28, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A79 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 79 3 where
 D := ![[2, 1], [66, 1], [48, 43, 11, 1]]; D' := ![[2, 1], [66, 1], [48, 43, 11, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6, 6]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P79P0
  | 1 => exact P79P1
  | 2 => exact P79P2

def C790 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A79.D 0) 79 where
  n := 1
  w := ![![79, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C791 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A79.D 1) 79 where
  n := 1
  w := ![![79, 0, 0, 0, 0], ![66, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C792 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A79.D 2) 79 where
  n := 3
  w := ![![79, 0, 0, 0, 0], ![48, 43, 11, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K79 : KummerData 79 ![I79N0, I79N1, I79N2] ![79, 79, 493039] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A79
  C := by
    intro i
    match i with
    | 0 => exact C790
    | 1 => exact C791
    | 2 => exact C792
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 79 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![72, 3, 1, 0, 0]] i)))

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![65, 78, 80, 5, 0]] i)))

def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [72, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 82], [0, 1]]
 g := ![![[45, 37], [24, 59], [12], [1], [73, 9], [1]], ![[17, 46], [13, 24], [12], [1], [46, 74], [1]]]
 h' := ![![[80, 82], [15, 55], [15, 15], [76, 26], [56, 1], [11, 80], [0, 1]], ![[0, 1], [16, 28], [53, 68], [81, 57], [53, 82], [20, 3], [80, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [25, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P83P1 : CertificateIrreducibleZModOfList' 83 3 2 6 [65, 78, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 74, 61], [75, 8, 22], [0, 1]]
 g := ![![[79, 36, 1], [16, 48, 59], [66, 68], [34, 64], [14, 3, 1], []], ![[16, 48, 68, 65], [19, 45, 5, 48], [72, 33], [4, 70], [59, 24, 8, 3], [22, 69]], ![[48, 22, 24, 24], [78, 64, 24, 43], [28, 75], [45, 69], [5, 64, 4, 39], [61, 69]]]
 h' := ![![[11, 74, 61], [39, 25, 82], [49, 4, 15], [40, 74, 63], [3, 41, 75], [0, 0, 1], [0, 1]], ![[75, 8, 22], [46, 32, 23], [46, 10, 32], [59, 75, 38], [53, 27, 30], [19, 75, 8], [11, 74, 61]], ![[0, 1], [5, 26, 61], [17, 69, 36], [29, 17, 65], [7, 15, 61], [0, 8, 74], [75, 8, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 72], []]
 b := ![[], [74, 61, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A83 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 83 2 where
 D := ![[72, 3, 1], [65, 78, 80, 1]]; D' := ![[72, 3, 1], [65, 78, 80, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P83P0
  | 1 => exact P83P1

def C830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A83.D 0) 83 where
  n := 2
  w := ![![83, 0, 0, 0, 0], ![72, 3, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A83.D 1) 83 where
  n := 3
  w := ![![83, 0, 0, 0, 0], ![65, 78, 80, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K83 : KummerData 83 ![I83N0, I83N1] ![6889, 571787] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A83
  C := by
    intro i
    match i with
    | 0 => exact C830
    | 1 => exact C831
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 83 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0], ![40, 1, 0, 0, 0]] i)))

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0], ![66, 1, 0, 0, 0]] i)))

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0], ![10, 27, 72, 5, 0]] i)))

def P89P0 : CertificateIrreducibleZModOfList' 89 1 2 6 [40, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [57], [4], [49, 1]]]
 h' := ![![[0, 1], [1], [88], [34], [18], [87], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P89P1 : CertificateIrreducibleZModOfList' 89 1 2 6 [66, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [79], [25], [23, 1]]]
 h' := ![![[0, 1], [88], [34], [37], [41], [84], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P89P2 : CertificateIrreducibleZModOfList' 89 3 2 6 [10, 27, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 31, 30], [45, 57, 59], [0, 1]]
 g := ![![[74, 83, 36], [54, 40], [13, 81], [21, 12, 44], [84, 17, 1], []], ![[88, 68, 62, 23], [47, 47], [14, 11], [12, 4, 40, 82], [55, 72, 54, 15], [72, 10]], ![[53, 26, 20, 60], [80, 18], [85, 1], [75, 15, 21, 14], [3, 18, 77, 6], [43, 10]]]
 h' := ![![[61, 31, 30], [10, 82, 6], [4, 20, 60], [57, 33, 9], [50, 54, 69], [0, 0, 1], [0, 1]], ![[45, 57, 59], [56, 65, 43], [80, 58, 15], [65, 22, 79], [17, 22, 35], [64, 47, 57], [61, 31, 30]], ![[0, 1], [9, 31, 40], [39, 11, 14], [55, 34, 1], [39, 13, 74], [82, 42, 31], [45, 57, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 15], []]
 b := ![[], [11, 32, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A89 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 89 3 where
 D := ![[40, 1], [66, 1], [10, 27, 72, 1]]; D' := ![[40, 1], [66, 1], [10, 27, 72, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6, 6]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P89P0
  | 1 => exact P89P1
  | 2 => exact P89P2

def C890 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A89.D 0) 89 where
  n := 1
  w := ![![89, 0, 0, 0, 0], ![40, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C891 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A89.D 1) 89 where
  n := 1
  w := ![![89, 0, 0, 0, 0], ![66, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C892 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A89.D 2) 89 where
  n := 3
  w := ![![89, 0, 0, 0, 0], ![10, 27, 72, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K89 : KummerData 89 ![I89N0, I89N1, I89N2] ![89, 89, 704969] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A89
  C := by
    intro i
    match i with
    | 0 => exact C890
    | 1 => exact C891
    | 2 => exact C892
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 89 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] i)))

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0], ![28, 1, 0, 0, 0]] i)))

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0], ![65, 1, 0, 0, 0]] i)))

def I97N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0], ![35, 94, 1, 0, 0]] i)))

def P97P0 : CertificateIrreducibleZModOfList' 97 1 2 6 [7, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [49, 90, 1]]]
 h' := ![![[0, 1], [96], [75], [47], [85], [45], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P97P1 : CertificateIrreducibleZModOfList' 97 1 2 6 [28, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [8, 69, 1]]]
 h' := ![![[0, 1], [96], [75], [50], [27], [67], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P97P2 : CertificateIrreducibleZModOfList' 97 1 2 6 [65, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [54, 32, 1]]]
 h' := ![![[0, 1], [1], [96], [22], [33], [79], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P97P3 : CertificateIrreducibleZModOfList' 97 2 2 6 [35, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 96], [0, 1]]
 g := ![![[11, 61], [6], [35], [70], [94], [3, 1]], ![[0, 36], [6], [35], [70], [94], [6, 96]]]
 h' := ![![[3, 96], [89, 35], [69, 43], [18, 36], [72, 19], [89, 71], [0, 1]], ![[0, 1], [0, 62], [4, 54], [29, 61], [32, 78], [11, 26], [3, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [37, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A97 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 97 4 where
 D := ![[7, 1], [28, 1], [65, 1], [35, 94, 1]]; D' := ![[7, 1], [28, 1], [65, 1], [35, 94, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6, 6, 6]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P97P0
  | 1 => exact P97P1
  | 2 => exact P97P2
  | 3 => exact P97P3

def C970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A97.D 0) 97 where
  n := 1
  w := ![![97, 0, 0, 0, 0], ![7, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A97.D 1) 97 where
  n := 1
  w := ![![97, 0, 0, 0, 0], ![28, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C972 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A97.D 2) 97 where
  n := 1
  w := ![![97, 0, 0, 0, 0], ![65, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C973 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A97.D 3) 97 where
  n := 2
  w := ![![97, 0, 0, 0, 0], ![35, 94, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K97 : KummerData 97 ![I97N0, I97N1, I97N2, I97N3] ![97, 97, 97, 9409] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A97
  C := by
    intro i
    match i with
    | 0 => exact C970
    | 1 => exact C971
    | 2 => exact C972
    | 3 => exact C973
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 97 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0], ![303, -202, 0, 505, 0]] i)))

def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [3, 48, 0, 76, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 44, 91, 29, 49], [68, 16, 37, 75, 68], [1, 35, 22, 29, 38], [59, 5, 52, 69, 47], [0, 1]]
 g := ![![[9, 3, 3, 60, 9], [37, 3, 16, 20], [42, 65, 75, 51, 92], [52, 95, 0, 19], [0, 1], []], ![[90, 93, 87, 99, 31, 54, 89, 71], [66, 65, 69, 52], [82, 82, 89, 44, 76, 96, 61, 54], [82, 59, 99, 77], [48, 41, 31, 17], [12, 84, 71, 62, 97, 91, 19, 85]], ![[59, 70, 62, 84, 89, 69, 99, 31], [35, 2, 80, 65], [93, 5, 29, 61, 8, 64, 69, 80], [25, 0, 98, 76], [19, 61, 84, 84], [92, 33, 82, 88, 18, 92, 100, 19]], ![[74, 63, 8, 92, 52, 82, 62, 53], [50, 25, 94, 70], [63, 92, 19, 9, 66, 22, 22, 93], [62, 12, 64, 79], [70, 10, 65, 84], [0, 33, 16, 0, 95, 3, 85, 29]], ![[43, 1, 85, 91, 36, 94, 79, 17], [84, 14, 17, 95], [15, 49, 4, 89, 29, 7, 90, 92], [67, 55, 48, 84], [24, 34, 32, 17], [23, 17, 60, 7, 53, 23, 36, 96]]]
 h' := ![![[74, 44, 91, 29, 49], [9, 36, 81, 10, 3], [76, 6, 70, 65, 11], [46, 47, 95, 16, 30], [0, 98, 53, 0, 25], [0, 0, 0, 1], [0, 1]], ![[68, 16, 37, 75, 68], [9, 50, 50, 80, 90], [45, 57, 71, 95, 70], [33, 24, 17, 64, 60], [28, 36, 15, 18, 28], [77, 56, 81, 49, 57], [74, 44, 91, 29, 49]], ![[1, 35, 22, 29, 38], [41, 97, 13, 44, 20], [67, 2, 38, 68, 60], [32, 69, 28, 73, 76], [39, 59, 10, 98, 51], [46, 85, 78, 18, 36], [68, 16, 37, 75, 68]], ![[59, 5, 52, 69, 47], [68, 54, 25, 32, 11], [97, 50, 61, 72, 75], [65, 42, 35, 3, 80], [94, 56, 44, 53, 33], [1, 6, 89, 51, 65], [1, 35, 22, 29, 38]], ![[0, 1], [72, 66, 33, 36, 78], [83, 87, 63, 3, 87], [83, 20, 27, 46, 57], [53, 54, 80, 33, 65], [78, 55, 55, 83, 44], [59, 5, 52, 69, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 79, 5, 67], [], [], []]
 b := ![[], [85, 87, 76, 14, 11], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A101 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 101 1 where
 D := ![[3, 48, 0, 76, 0, 1]]; D' := ![[3, 48, 0, 76, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P101P0

def C1010 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A101.D 0) 101 where
  n := 5
  w := ![![101, 0, 0, 0, 0], ![303, -202, 0, 505, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K101 : KummerData 101 ![I101N0] ![10510100501] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A101
  C := by
    intro i
    match i with
    | 0 => exact C1010
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 101 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![13, 1, 0, 0, 0]] i)))

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![96, 1, 0, 0, 0]] i)))

def I103N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![26, 94, 1, 0, 0]] i)))

def P103P0 : CertificateIrreducibleZModOfList' 103 1 2 6 [3, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [34], [79], [], [], [9, 100, 1]]]
 h' := ![![[0, 1], [1], [72], [64], [8], [76], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P103P1 : CertificateIrreducibleZModOfList' 103 1 2 6 [13, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [8], [93], [], [], [66, 90, 1]]]
 h' := ![![[0, 1], [102], [27], [14], [23], [69], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P103P2 : CertificateIrreducibleZModOfList' 103 1 2 6 [96, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [59], [93], [], [], [49, 7, 1]]]
 h' := ![![[0, 1], [1], [33], [14], [23], [34], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P103P3 : CertificateIrreducibleZModOfList' 103 2 2 6 [26, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 102], [0, 1]]
 g := ![![[67, 4], [72, 64], [80, 61], [98], [38], [9, 1]], ![[0, 99], [30, 39], [11, 42], [98], [38], [18, 102]]]
 h' := ![![[9, 102], [85, 2], [83, 95], [31, 24], [2, 43], [75, 55], [0, 1]], ![[0, 1], [0, 101], [11, 8], [41, 79], [80, 60], [55, 48], [9, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [22, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A103 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 103 4 where
 D := ![[3, 1], [13, 1], [96, 1], [26, 94, 1]]; D' := ![[3, 1], [13, 1], [96, 1], [26, 94, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6, 6, 6]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P103P0
  | 1 => exact P103P1
  | 2 => exact P103P2
  | 3 => exact P103P3

def C1030 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A103.D 0) 103 where
  n := 1
  w := ![![103, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1031 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A103.D 1) 103 where
  n := 1
  w := ![![103, 0, 0, 0, 0], ![13, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1032 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A103.D 2) 103 where
  n := 1
  w := ![![103, 0, 0, 0, 0], ![96, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1033 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A103.D 3) 103 where
  n := 2
  w := ![![103, 0, 0, 0, 0], ![26, 94, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K103 : KummerData 103 ![I103N0, I103N1, I103N2, I103N3] ![103, 103, 103, 10609] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A103
  C := by
    intro i
    match i with
    | 0 => exact C1030
    | 1 => exact C1031
    | 2 => exact C1032
    | 3 => exact C1033
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 103 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)
  decide

def PB1045I2 : PrimesBelowBoundCertificateInterval O 61 103 1045 where
  m := 9
  g := ![2, 1, 2, 3, 2, 3, 4, 1, 4]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1045I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2, I97N3]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2, I103N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K67) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K71) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K73) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K79) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K83) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K89) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K97) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K101) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K103) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![67, 20151121]
    · exact ![1804229351]
    · exact ![73, 28398241]
    · exact ![79, 79, 493039]
    · exact ![6889, 571787]
    · exact ![89, 89, 704969]
    · exact ![97, 97, 97, 9409]
    · exact ![10510100501]
    · exact ![103, 103, 103, 10609]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K67)
    · exact (card_quot_of_KummerData K71)
    · exact (card_quot_of_KummerData K73)
    · exact (card_quot_of_KummerData K79)
    · exact (card_quot_of_KummerData K83)
    · exact (card_quot_of_KummerData K89)
    · exact (card_quot_of_KummerData K97)
    · exact (card_quot_of_KummerData K101)
    · exact (card_quot_of_KummerData K103)
  β := ![I67N0, I73N0, I79N0, I79N1, I89N0, I89N1, I97N0, I97N1, I97N2, I103N0, I103N1, I103N2]
  Il := ![[I67N0], [], [I73N0], [I79N0, I79N1], [], [I89N0, I89N1], [I97N0, I97N1, I97N2], [], [I103N0, I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
