
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![14, 46, 1, 0, 0]] i)))

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![64, 26, 21, 2, 0]] i)))

def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [14, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 66], [0, 1]]
 g := ![![[32, 24], [11, 25], [60], [29], [39], [1]], ![[0, 43], [0, 42], [60], [29], [39], [1]]]
 h' := ![![[21, 66], [47, 52], [29, 5], [20, 44], [52, 30], [53, 21], [0, 1]], ![[0, 1], [0, 15], [0, 62], [6, 23], [12, 37], [25, 46], [21, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [50, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P67P1 : CertificateIrreducibleZModOfList' 67 3 2 6 [64, 25, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40, 54], [44, 26, 13], [0, 1]]
 g := ![![[23, 19, 40], [53, 44, 23], [20, 62], [15, 62], [46, 1], []], ![[1, 37, 55, 56], [26, 13, 54, 39], [18, 60], [48, 1], [6, 6], [34, 35]], ![[7, 27, 62, 52], [6, 30, 44, 43], [66, 29], [36, 35], [1, 59], [8, 35]]]
 h' := ![![[2, 40, 54], [25, 50, 24], [29, 42, 31], [61, 15, 53], [4, 59, 14], [0, 0, 1], [0, 1]], ![[44, 26, 13], [56, 20, 41], [49, 27, 59], [14, 13, 44], [65, 66, 66], [39, 18, 26], [2, 40, 54]], ![[0, 1], [20, 64, 2], [59, 65, 44], [14, 39, 37], [24, 9, 54], [17, 49, 40], [44, 26, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 56], []]
 b := ![[], [5, 16, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A67 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 67 2 where
 D := ![[14, 46, 1], [64, 25, 21, 1]]; D' := ![[14, 46, 1], [64, 25, 21, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P67P0
  | 1 => exact P67P1

def C670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A67.D 0) 67 where
  n := 2
  w := ![![67, 0, 0, 0, 0], ![14, 46, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A67.D 1) 67 where
  n := 3
  w := ![![67, 0, 0, 0, 0], ![64, 26, 21, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K67 : KummerData 67 ![I67N0, I67N1] ![4489, 300763] where
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![19, 1, 0, 0, 0]] i)))

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![57, 1, 0, 0, 0]] i)))

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![26, 8, 66, 2, 0]] i)))

def P71P0 : CertificateIrreducibleZModOfList' 71 1 2 6 [19, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [15], [40], [], [], [52, 1]]]
 h' := ![![[0, 1], [70], [21], [18], [36], [6], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P71P1 : CertificateIrreducibleZModOfList' 71 1 2 6 [57, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [5], [57], [], [], [14, 1]]]
 h' := ![![[0, 1], [70], [17], [25], [5], [54], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P71P2 : CertificateIrreducibleZModOfList' 71 3 2 6 [26, 7, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 51, 8], [23, 19, 63], [0, 1]]
 g := ![![[28, 33, 37], [43, 55, 57], [29, 2, 1], [63, 40], [5, 1], []], ![[9, 21, 11, 19], [16, 20, 20, 32], [38, 70, 0, 37], [18, 16], [13, 6], [0, 64]], ![[48, 24, 1, 11], [6, 32, 61, 28], [30, 47, 39, 56], [57, 54], [24, 45], [16, 64]]]
 h' := ![![[53, 51, 8], [18, 63, 45], [27, 38, 25], [68, 37, 70], [12, 10, 18], [0, 0, 1], [0, 1]], ![[23, 19, 63], [45, 67, 10], [59, 64, 69], [1, 62, 64], [55, 61, 67], [40, 50, 19], [53, 51, 8]], ![[0, 1], [20, 12, 16], [34, 40, 48], [25, 43, 8], [4, 0, 57], [42, 21, 51], [23, 19, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 36], []]
 b := ![[], [52, 41, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A71 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 71 3 where
 D := ![[19, 1], [57, 1], [26, 7, 66, 1]]; D' := ![[19, 1], [57, 1], [26, 7, 66, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6, 6]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P71P0
  | 1 => exact P71P1
  | 2 => exact P71P2

def C710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A71.D 0) 71 where
  n := 1
  w := ![![71, 0, 0, 0, 0], ![19, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C711 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A71.D 1) 71 where
  n := 1
  w := ![![71, 0, 0, 0, 0], ![57, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C712 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A71.D 2) 71 where
  n := 3
  w := ![![71, 0, 0, 0, 0], ![26, 8, 66, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K71 : KummerData 71 ![I71N0, I71N1, I71N2] ![71, 71, 357911] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A71
  C := by
    intro i
    match i with
    | 0 => exact C710
    | 1 => exact C711
    | 2 => exact C712
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 71 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0], ![69, 1, 0, 0, 0]] i)))

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0], ![709, 2143, 10911, -3030, 22728]] i)))

def P73P0 : CertificateIrreducibleZModOfList' 73 1 2 6 [69, 1] where
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
 g := ![![[], [], [], [55], [], [4, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [37], [16], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P73P1 : CertificateIrreducibleZModOfList' 73 4 2 6 [61, 37, 16, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 1, 10, 25], [37, 18, 44, 41], [7, 53, 19, 7], [0, 1]]
 g := ![![[69, 71, 69, 36], [30, 40, 57], [67, 69, 54], [42, 40, 64, 16], [1], []], ![[52, 9, 56, 13, 58, 24], [11, 21, 9], [3, 58, 16], [41, 72, 8, 8, 41, 24], [58, 58, 41], [48, 44, 41]], ![[6, 59, 37, 6, 30, 46], [22, 15, 4], [11, 71, 8], [29, 32, 58, 52, 70, 67], [69, 61, 9], [3, 23, 2]], ![[13, 68, 62, 47, 5, 31], [12, 6, 24], [54, 67, 6], [2, 46, 4, 29, 42, 44], [57, 44, 54], [39, 70, 49]]]
 h' := ![![[25, 1, 10, 25], [13, 25, 37, 67], [50, 54, 65, 38], [66, 19, 64, 45], [12, 36, 57, 69], [0, 0, 1], [0, 1]], ![[37, 18, 44, 41], [55, 4, 29, 6], [54, 40, 46, 3], [50, 42, 70, 4], [33, 1, 36, 6], [33, 43, 57, 25], [25, 1, 10, 25]], ![[7, 53, 19, 7], [69, 16, 8, 33], [43, 50, 26, 2], [38, 63, 26, 9], [57, 22, 12, 60], [18, 37, 4, 3], [37, 18, 44, 41]], ![[0, 1], [70, 28, 72, 40], [27, 2, 9, 30], [67, 22, 59, 15], [63, 14, 41, 11], [6, 66, 11, 45], [7, 53, 19, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [67, 27, 58], []]
 b := ![[], [], [4, 7, 18, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A73 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 73 2 where
 D := ![[69, 1], [61, 37, 16, 4, 1]]; D' := ![[69, 1], [61, 37, 16, 4, 1]]
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
  w := ![![73, 0, 0, 0, 0], ![69, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A73.D 1) 73 where
  n := 4
  w := ![![73, 0, 0, 0, 0], ![709, 2143, 10911, -3030, 22728]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![57, 1, 0, 0, 0]] i)))

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![73, 1, 0, 0, 0]] i)))

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![3, 21, 28, 2, 0]] i)))

def P79P0 : CertificateIrreducibleZModOfList' 79 1 2 6 [57, 1] where
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
 g := ![![[], [18], [67], [46], [], [22, 1]]]
 h' := ![![[0, 1], [1], [52], [64], [21], [10], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P79P1 : CertificateIrreducibleZModOfList' 79 1 2 6 [73, 1] where
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
 g := ![![[], [13], [8], [76], [], [6, 1]]]
 h' := ![![[0, 1], [78], [48], [61], [32], [36], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P79P2 : CertificateIrreducibleZModOfList' 79 3 2 6 [3, 20, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 54, 2], [26, 24, 77], [0, 1]]
 g := ![![[18, 55, 40], [14, 2, 42], [52, 22, 42], [12, 61, 44], [51, 1], []], ![[35, 71, 54, 16], [0, 9, 69, 51], [34, 4, 69, 13], [16, 71, 2, 38], [21, 23], [25, 4]], ![[29, 71, 25, 54], [46, 25, 41, 48], [76, 52, 4, 6], [26, 27, 48, 37], [23, 72], [29, 4]]]
 h' := ![![[25, 54, 2], [37, 34, 44], [2, 32, 11], [43, 76, 11], [5, 4, 53], [0, 0, 1], [0, 1]], ![[26, 24, 77], [44, 69, 18], [58, 42, 12], [14, 48, 21], [25, 50, 16], [76, 55, 24], [25, 54, 2]], ![[0, 1], [56, 55, 17], [45, 5, 56], [45, 34, 47], [42, 25, 10], [36, 24, 54], [26, 24, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 64], []]
 b := ![[], [48, 7, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A79 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 79 3 where
 D := ![[57, 1], [73, 1], [3, 20, 28, 1]]; D' := ![[57, 1], [73, 1], [3, 20, 28, 1]]
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
  w := ![![79, 0, 0, 0, 0], ![57, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C791 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A79.D 1) 79 where
  n := 1
  w := ![![79, 0, 0, 0, 0], ![73, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C792 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A79.D 2) 79 where
  n := 3
  w := ![![79, 0, 0, 0, 0], ![3, 21, 28, 2, 0]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![64, 1, 0, 0, 0]] i)))

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![724, 2157, 10924, -3000, 22728]] i)))

def P83P0 : CertificateIrreducibleZModOfList' 83 1 2 6 [64, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [48], [], [], [11], [19, 1]]]
 h' := ![![[0, 1], [82], [31], [23], [43], [29], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P83P1 : CertificateIrreducibleZModOfList' 83 4 2 6 [76, 36, 29, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 43, 28, 7], [31, 22, 3, 68], [42, 17, 52, 8], [0, 1]]
 g := ![![[58, 30, 12, 51], [63, 34, 48, 33], [62, 12, 64], [40], [64, 1], []], ![[66, 79, 43, 42, 40, 77], [17, 21, 62, 72, 26, 29], [64, 24, 69], [28, 22, 63], [37, 51, 59, 67, 58, 16], [80, 42, 49]], ![[56, 74, 80, 41, 12, 28], [61, 13, 19, 80, 53, 33], [5, 8, 25], [33, 34, 23], [52, 52, 0, 34, 17, 17], [63, 34, 59]], ![[25, 0, 14, 13, 52, 54], [43, 8, 81, 59, 29, 19], [57, 43, 29], [28, 42, 64], [37, 69, 63, 79, 66, 42], [33, 31, 64]]]
 h' := ![![[74, 43, 28, 7], [26, 68, 24, 36], [40, 0, 34, 38], [41, 10, 27, 75], [33, 27, 17], [0, 0, 1], [0, 1]], ![[31, 22, 3, 68], [54, 71, 59, 54], [9, 31, 69, 4], [15, 75, 36, 22], [63, 66, 81, 48], [60, 43, 14, 21], [74, 43, 28, 7]], ![[42, 17, 52, 8], [12, 53, 82, 15], [0, 78, 70, 23], [52, 61, 40, 5], [53, 62, 74, 43], [74, 81, 24, 41], [31, 22, 3, 68]], ![[0, 1], [27, 57, 1, 61], [45, 57, 76, 18], [12, 20, 63, 64], [56, 11, 77, 75], [3, 42, 44, 21], [42, 17, 52, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [65, 1, 29], []]
 b := ![[], [], [4, 80, 56, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A83 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 83 2 where
 D := ![[64, 1], [76, 36, 29, 19, 1]]; D' := ![[64, 1], [76, 36, 29, 19, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P83P0
  | 1 => exact P83P1

def C830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A83.D 0) 83 where
  n := 1
  w := ![![83, 0, 0, 0, 0], ![64, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A83.D 1) 83 where
  n := 4
  w := ![![83, 0, 0, 0, 0], ![724, 2157, 10924, -3000, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K83 : KummerData 83 ![I83N0, I83N1] ![83, 47458321] where
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0], ![35, 1, 0, 0, 0]] i)))

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0], ![16, 59, 1, 0, 0]] i)))

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0], ![80, 84, 1, 0, 0]] i)))

def P89P0 : CertificateIrreducibleZModOfList' 89 1 2 6 [35, 1] where
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
 g := ![![[], [], [], [20], [85], [54, 1]]]
 h' := ![![[0, 1], [88], [55], [12], [51], [68], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [16, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 88], [0, 1]]
 g := ![![[76, 39], [1], [40], [27, 68], [52, 10], [1]], ![[0, 50], [1], [40], [20, 21], [85, 79], [1]]]
 h' := ![![[30, 88], [37, 67], [63, 1], [13, 60], [58, 54], [73, 30], [0, 1]], ![[0, 1], [0, 22], [4, 88], [33, 29], [76, 35], [83, 59], [30, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [39, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P89P2 : CertificateIrreducibleZModOfList' 89 2 2 6 [80, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 88], [0, 1]]
 g := ![![[50, 79], [53], [20], [9, 69], [37, 25], [1]], ![[0, 10], [53], [20], [87, 20], [73, 64], [1]]]
 h' := ![![[5, 88], [27, 48], [66, 26], [81, 38], [66, 46], [9, 5], [0, 1]], ![[0, 1], [0, 41], [18, 63], [4, 51], [29, 43], [34, 84], [5, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [3, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A89 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 89 3 where
 D := ![[35, 1], [16, 59, 1], [80, 84, 1]]; D' := ![[35, 1], [16, 59, 1], [80, 84, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6, 6]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P89P0
  | 1 => exact P89P1
  | 2 => exact P89P2

def C890 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A89.D 0) 89 where
  n := 1
  w := ![![89, 0, 0, 0, 0], ![35, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C891 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A89.D 1) 89 where
  n := 2
  w := ![![89, 0, 0, 0, 0], ![16, 59, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C892 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A89.D 2) 89 where
  n := 2
  w := ![![89, 0, 0, 0, 0], ![80, 84, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K89 : KummerData 89 ![I89N0, I89N1, I89N2] ![89, 7921, 7921] where
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0], ![33, 93, 1, 0, 0]] i)))

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0], ![88, 81, 4, 2, 0]] i)))

def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [33, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 96], [0, 1]]
 g := ![![[91, 50], [16], [73], [33], [95], [4, 1]], ![[0, 47], [16], [73], [33], [95], [8, 96]]]
 h' := ![![[4, 96], [86, 27], [41, 93], [5, 48], [30, 18], [62, 80], [0, 1]], ![[0, 1], [0, 70], [25, 4], [3, 49], [5, 79], [91, 17], [4, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [10, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P97P1 : CertificateIrreducibleZModOfList' 97 3 2 6 [88, 80, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 87, 15], [2, 9, 82], [0, 1]]
 g := ![![[64, 7, 27], [17, 54], [87, 95], [56, 8], [91, 16], [1]], ![[43, 22, 10, 34], [23, 32], [54, 81], [15, 48], [75, 43], [77, 18, 23, 77]], ![[47, 77, 6, 55], [56, 91], [50, 64], [16, 65], [46, 53], [80, 61, 78, 20]]]
 h' := ![![[91, 87, 15], [87, 87, 67], [15, 87, 32], [69, 28, 17], [27, 57, 28], [9, 17, 93], [0, 1]], ![[2, 9, 82], [57, 88, 65], [74, 74, 41], [49, 76, 88], [60, 62, 40], [89, 3, 25], [91, 87, 15]], ![[0, 1], [15, 19, 62], [44, 33, 24], [51, 90, 89], [2, 75, 29], [49, 77, 76], [2, 9, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 58], []]
 b := ![[], [70, 16, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A97 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 97 2 where
 D := ![[33, 93, 1], [88, 80, 4, 1]]; D' := ![[33, 93, 1], [88, 80, 4, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P97P0
  | 1 => exact P97P1

def C970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A97.D 0) 97 where
  n := 2
  w := ![![97, 0, 0, 0, 0], ![33, 93, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A97.D 1) 97 where
  n := 3
  w := ![![97, 0, 0, 0, 0], ![88, 81, 4, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K97 : KummerData 97 ![I97N0, I97N1] ![9409, 912673] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A97
  C := by
    intro i
    match i with
    | 0 => exact C970
    | 1 => exact C971
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 97 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0], ![82, 1, 0, 0, 0]] i)))

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0], ![16, 6, 1, 0, 0]] i)))

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0], ![65, 13, 1, 0, 0]] i)))

def P101P0 : CertificateIrreducibleZModOfList' 101 1 2 6 [82, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [16], [], [], [58, 19, 1]]]
 h' := ![![[0, 1], [1], [1], [97], [81], [92], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [16, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 100], [0, 1]]
 g := ![![[13, 19], [92], [44, 45], [70], [97], [95, 1]], ![[0, 82], [92], [77, 56], [70], [97], [89, 100]]]
 h' := ![![[95, 100], [52, 76], [3, 71], [34, 67], [89, 26], [96, 20], [0, 1]], ![[0, 1], [0, 25], [82, 30], [36, 34], [34, 75], [77, 81], [95, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [94, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P101P2 : CertificateIrreducibleZModOfList' 101 2 2 6 [65, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 100], [0, 1]]
 g := ![![[81, 14], [100], [19, 16], [16], [9], [88, 1]], ![[0, 87], [100], [13, 85], [16], [9], [75, 100]]]
 h' := ![![[88, 100], [89, 69], [78, 91], [41, 4], [77, 4], [37, 3], [0, 1]], ![[0, 1], [0, 32], [6, 10], [90, 97], [25, 97], [99, 98], [88, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [29, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A101 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 101 3 where
 D := ![[82, 1], [16, 6, 1], [65, 13, 1]]; D' := ![[82, 1], [16, 6, 1], [65, 13, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6, 6]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P101P0
  | 1 => exact P101P1
  | 2 => exact P101P2

def C1010 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A101.D 0) 101 where
  n := 1
  w := ![![101, 0, 0, 0, 0], ![82, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1011 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A101.D 1) 101 where
  n := 2
  w := ![![101, 0, 0, 0, 0], ![16, 6, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1012 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A101.D 2) 101 where
  n := 2
  w := ![![101, 0, 0, 0, 0], ![65, 13, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K101 : KummerData 101 ![I101N0, I101N1, I101N2] ![101, 10201, 10201] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A101
  C := by
    intro i
    match i with
    | 0 => exact C1010
    | 1 => exact C1011
    | 2 => exact C1012
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 101 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![77, 66, 1, 0, 0]] i)))

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![50, 57, 37, 2, 0]] i)))

def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [77, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 102], [0, 1]]
 g := ![![[45, 36], [17, 16], [30, 72], [98], [46], [37, 1]], ![[38, 67], [94, 87], [16, 31], [98], [46], [74, 102]]]
 h' := ![![[37, 102], [30, 97], [59, 99], [102, 81], [52, 60], [35, 56], [0, 1]], ![[0, 1], [14, 6], [14, 4], [9, 22], [6, 43], [47, 47], [37, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [61, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P103P1 : CertificateIrreducibleZModOfList' 103 3 2 6 [50, 56, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 55, 12], [102, 47, 91], [0, 1]]
 g := ![![[79, 3, 25], [90, 72, 100], [93, 99, 9], [72, 15], [47, 30], [1]], ![[39, 82, 32, 10], [73, 0, 38, 86], [46, 48, 51, 84], [22, 7], [83, 13], [45, 98, 97, 80]], ![[45, 55, 91, 83], [7, 22, 12, 92], [18, 13, 67, 63], [78, 98], [74, 61], [98, 26, 89, 23]]]
 h' := ![![[67, 55, 12], [32, 31, 5], [88, 65, 10], [51, 31, 100], [47, 26, 18], [53, 47, 66], [0, 1]], ![[102, 47, 91], [56, 35, 92], [28, 29, 14], [2, 29, 25], [22, 53, 25], [19, 8, 61], [67, 55, 12]], ![[0, 1], [99, 37, 6], [13, 9, 79], [23, 43, 81], [3, 24, 60], [43, 48, 79], [102, 47, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 20], []]
 b := ![[], [34, 94, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A103 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 103 2 where
 D := ![[77, 66, 1], [50, 56, 37, 1]]; D' := ![[77, 66, 1], [50, 56, 37, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P103P0
  | 1 => exact P103P1

def C1030 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A103.D 0) 103 where
  n := 2
  w := ![![103, 0, 0, 0, 0], ![77, 66, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1031 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A103.D 1) 103 where
  n := 3
  w := ![![103, 0, 0, 0, 0], ![50, 57, 37, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K103 : KummerData 103 ![I103N0, I103N1] ![10609, 1092727] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A103
  C := by
    intro i
    match i with
    | 0 => exact C1030
    | 1 => exact C1031
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 103 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)
  decide

def PB18792I2 : PrimesBelowBoundCertificateInterval O 61 103 18792 where
  m := 9
  g := ![2, 3, 2, 3, 2, 3, 2, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB18792I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
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
    · exact ![4489, 300763]
    · exact ![71, 71, 357911]
    · exact ![73, 28398241]
    · exact ![79, 79, 493039]
    · exact ![83, 47458321]
    · exact ![89, 7921, 7921]
    · exact ![9409, 912673]
    · exact ![101, 10201, 10201]
    · exact ![10609, 1092727]
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
  β := ![I67N0, I71N0, I71N1, I73N0, I79N0, I79N1, I83N0, I89N0, I89N1, I89N2, I97N0, I101N0, I101N1, I101N2, I103N0]
  Il := ![[I67N0], [I71N0, I71N1], [I73N0], [I79N0, I79N1], [I83N0], [I89N0, I89N1, I89N2], [I97N0], [I101N0, I101N1, I101N2], [I103N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
