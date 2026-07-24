
import IdealArithmetic.Examples.NF5_1_16200000_1.RI5_1_16200000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [22, 2, 14, 14, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 22, 16, 16, 9], [5, 0, 12, 17, 28], [16, 21, 28, 16, 14], [14, 14, 2, 9, 7], [0, 1]]
 g := ![![[10, 28, 19, 11, 16], [14, 9, 18, 20], [20, 18, 1], []], ![[23, 5, 16, 12, 12, 28], [12, 11, 15, 7], [22, 19, 3, 18, 27, 24, 21, 4], [7, 8, 21, 15, 2, 12, 16, 4]], ![[27, 28, 26, 0, 10, 6, 4, 20], [8, 3, 24, 16], [16, 21, 13, 10, 4, 23, 8, 25], [17, 4, 23, 11, 10, 9, 4, 28]], ![[7, 23, 28, 24, 5, 14], [22, 23, 9, 20], [0, 3, 7, 25, 4, 9, 27, 27], [15, 21, 1, 10, 0, 10, 17, 18]], ![[18, 15, 0, 10, 15, 0, 17, 24], [21, 10, 22, 28], [28, 1, 1, 26, 23, 26, 13, 1], [10, 7, 2, 22, 19, 15, 15, 24]]]
 h' := ![![[12, 22, 16, 16, 9], [7, 16, 16, 27, 4], [24, 28, 10, 17, 7], [0, 0, 0, 1], [0, 1]], ![[5, 0, 12, 17, 28], [4, 4, 17, 4], [23, 21, 21, 2, 23], [8, 5, 9, 11, 20], [12, 22, 16, 16, 9]], ![[16, 21, 28, 16, 14], [21, 20, 5, 22, 3], [20, 4, 5, 25, 4], [12, 23, 3, 26, 2], [5, 0, 12, 17, 28]], ![[14, 14, 2, 9, 7], [5, 18, 2, 1], [24, 7, 22, 6, 7], [25, 5, 0, 15, 2], [16, 21, 28, 16, 14]], ![[0, 1], [22, 0, 18, 4, 22], [7, 27, 0, 8, 17], [1, 25, 17, 5, 5], [14, 14, 2, 9, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 16, 16, 1], [], [], []]
 b := ![[], [23, 5, 6, 4, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [22, 2, 14, 14, 11, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1293400524610, -485198336770, -1624845923156, 146034507314, -2238651034366]
  a := ![0, 36, -63, 23, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-44600018090, -16730977130, -56029169764, 5035672666, -77194863254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [3, 11, 13, 3, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 29, 13, 9, 10], [27, 20, 26, 19, 14], [8, 9, 19, 20, 24], [17, 3, 4, 14, 14], [0, 1]]
 g := ![![[4, 10, 5], [16, 14, 17, 7, 28], [16, 9, 1], []], ![[13, 17, 27, 29, 2, 14, 0, 10], [5, 15, 16, 16, 8, 28, 18, 20], [29, 19, 19, 2, 11, 26, 5, 28], [7, 11, 20, 9, 23, 6, 13, 8]], ![[6, 22, 13, 6, 27, 7, 24, 18], [6, 24, 16, 19, 8, 7, 0, 20], [9, 4, 23, 25, 22, 7, 14, 5], [11, 2, 6, 12, 12, 0, 1, 16]], ![[6, 6, 23, 29, 6, 8, 23, 27], [20, 19, 26, 5, 2, 25, 27, 26], [22, 6, 10, 4, 26, 17, 4, 12], [20, 29, 24, 12, 24, 20, 8, 29]], ![[20, 1, 3, 12, 16, 0, 20, 7], [21, 7, 3, 21, 21, 11, 15, 1], [11, 30, 3, 10, 3, 23, 24, 16], [9, 0, 16, 8, 12, 19, 6, 16]]]
 h' := ![![[19, 29, 13, 9, 10], [14, 9, 10, 6], [14, 14, 0, 10, 11], [0, 0, 0, 1], [0, 1]], ![[27, 20, 26, 19, 14], [17, 9, 1, 9, 1], [24, 4, 12, 26, 8], [18, 18, 23, 9, 3], [19, 29, 13, 9, 10]], ![[8, 9, 19, 20, 24], [28, 10, 21, 7, 9], [2, 19, 3, 15, 11], [27, 27, 16, 22, 10], [27, 20, 26, 19, 14]], ![[17, 3, 4, 14, 14], [4, 18, 12, 8, 25], [15, 7, 29, 10, 13], [18, 26, 12, 12, 4], [8, 9, 19, 20, 24]], ![[0, 1], [28, 16, 18, 1, 27], [28, 18, 18, 1, 19], [19, 22, 11, 18, 14], [17, 3, 4, 14, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 18, 20, 19], [], [], []]
 b := ![[], [28, 29, 13, 1, 26], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [3, 11, 13, 3, 22, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-989385640763438925, -373727687274794837, -1247102651262577025, 110717405073673946, -1716285312295077680]
  a := ![3, 431, -805, 243, -1672]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31915665831078675, -12055731847574027, -40229117782663775, 3571529195924966, -55364042332099280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 32, -35, 32, -95]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-79, 32, -35, 32, -95]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![25, 32, 10, 1, 0], ![26, 12, 31, 0, 1]] where
  M :=![![![-79, 32, -35, 32, -95], ![-190, -243, 99, -40, 293], ![586, -104, 196, -188, 505], ![600, 918, -378, 181, -1140], ![-294, 172, -161, 138, -440]]]
  hmulB := by decide  
  f := ![![![93, 0, -5, 2, -31]], ![![-62, 105, -71, 42, -107]], ![![-214, -320, 246, -138, 473]], ![![-35, 10, -3, 3, 3]], ![![-130, -228, 175, -98, 331]]]
  g := ![![![43, 4, 70, 32, -95], ![-184, -67, -232, -40, 293], ![-212, -4, -367, -188, 505], ![695, 238, 896, 181, -1140], ![208, 28, 327, 138, -440]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [25, 27, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 12], [10, 31, 25], [0, 1]]
 g := ![![[34, 22, 21], [14, 33], [0, 30, 30], [11, 1], []], ![[28, 33, 18, 11], [31, 36], [23, 17, 5, 26], [20, 36], [2, 33]], ![[1, 9, 14, 1], [13, 36], [13, 4, 9, 33], [11, 25], [26, 33]]]
 h' := ![![[1, 5, 12], [20, 18, 24], [0, 24, 12], [21, 11, 20], [0, 0, 1], [0, 1]], ![[10, 31, 25], [9, 28, 35], [28, 15, 31], [14, 28, 12], [25, 19, 31], [1, 5, 12]], ![[0, 1], [24, 28, 15], [4, 35, 31], [9, 35, 5], [5, 18, 5], [10, 31, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 35], []]
 b := ![[], [9, 33, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [25, 27, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6992411, -2285444, -9302495, 916430, -13147521]
  a := ![1, 34, -62, 20, -129]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8430605, 3409704, 10516388, 916430, -13147521]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, 0, 5, -2, 31]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-93, 0, 5, -2, 31]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![4, 17, 1, 0, 0], ![3, 6, 0, 1, 0], ![24, 6, 0, 0, 1]] where
  M :=![![![-93, 0, 5, -2, 31], ![62, -105, 71, -42, 107], ![214, 320, -246, 138, -473], ![-504, -210, 174, -97, 420], ![-150, -224, 169, -96, 326]]]
  hmulB := by decide  
  f := ![![![79, -32, 35, -32, 95]], ![![190, 243, -99, 40, -293]], ![![80, 111, -47, 20, -138]], ![![21, 12, -3, -1, -9]], ![![90, 14, 11, -18, 26]]]
  g := ![![![-23, -7, 5, -2, 31], ![-72, -46, 71, -42, 107], ![328, 176, -246, 138, -473], ![-297, -138, 174, -97, 420], ![-226, -121, 169, -96, 326]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [8, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 36], [0, 1]]
 g := ![![[6, 34], [26], [33, 27], [10], [1]], ![[2, 3], [26], [32, 10], [10], [1]]]
 h' := ![![[26, 36], [2, 21], [32, 10], [21, 29], [29, 26], [0, 1]], ![[0, 1], [30, 16], [33, 27], [35, 8], [2, 11], [26, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [19, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [8, 11, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44926, 14960, 20172, -2916, 26720]
  a := ![-1, 70, -111, 53, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18062, -12724, 20172, -2916, 26720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-79, 32, -35, 32, -95]] ![![-93, 0, 5, -2, 31]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-415, -201, -556, 30, -731]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-415, -201, -556, 30, -731]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![36, 29, 20, 1, 0], ![9, 11, 34, 0, 1]] where
  M :=![![![-415, -201, -556, 30, -731], ![-1462, -450, -2064, 200, -2935], ![-5870, -1991, -7055, 742, -9875], ![-9144, -3897, -10695, 865, -14316], ![-834, -513, -1152, 20, -1430]]]
  hmulB := by decide  
  f := ![![![1521, 1255, -990, 554, -2063]], ![![-4126, -1284, 1160, -624, 2981]], ![![5962, -1579, 795, -522, -71]], ![![1374, -433, 233, -149, 69]], ![![4069, -1352, 740, -470, 290]]]
  g := ![![![124, 170, 578, 30, -731], ![433, 635, 2286, 200, -2935], ![1373, 2076, 7655, 742, -9875], ![2160, 3134, 11189, 865, -14316], ![276, 357, 1148, 20, -1430]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [19, 18, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 5, 17], [29, 35, 24], [0, 1]]
 g := ![![[2, 14, 40], [3, 33], [26, 32], [22, 32, 1], []], ![[38, 40, 19, 38], [6, 18], [13, 18], [27, 40, 5, 38], [29, 2]], ![[20, 25, 39, 11], [34, 40], [9, 2], [5, 15, 3, 26], [22, 2]]]
 h' := ![![[3, 5, 17], [15, 39, 9], [21, 23, 19], [33, 21, 27], [0, 0, 1], [0, 1]], ![[29, 35, 24], [10, 17, 35], [1, 8, 31], [17, 22, 31], [32, 3, 35], [3, 5, 17]], ![[0, 1], [33, 26, 38], [33, 10, 32], [9, 39, 24], [13, 38, 5], [29, 35, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 24], []]
 b := ![[], [9, 19, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [19, 18, 9, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1431789, 122972, -483492, 563800, -1811328]
  a := ![0, -42, 54, -42, 112]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-132357, 90180, 1215260, 563800, -1811328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59507, 12297, -5442, 3774, 4979]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-59507, 12297, -5442, 3774, 4979]] 
 ![![41, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-59507, 12297, -5442, 3774, 4979], ![9958, -96346, 68748, -39712, 115471], ![230942, 241219, -186765, 105114, -375733], ![-380712, -109771, 100763, -53961, 264300], ![-160234, -168467, 130376, -73388, 262054]]]
  hmulB := by decide  
  f := ![![![7821, 4841, -3392, -254, -6889]], ![![1190, 1264, -1116, 152, -2333]], ![![1456, 913, -1919, -50, -3131]], ![![1206, -817, -697, -615, -42]], ![![2237, 1280, -764, -110, -1591]]]
  g := ![![![-2864, 12297, -5442, 3774, 4979], ![-25043, -96346, 68748, -39712, 115471], ![89327, 241219, -186765, 105114, -375733], ![-69332, -109771, 100763, -53961, 264300], ![-62276, -168467, 130376, -73388, 262054]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 10, 8, -12, 18]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![61, 10, 8, -12, 18]] 
 ![![41, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![61, 10, 8, -12, 18], ![36, 135, -68, 40, -198], ![-396, -114, -19, 60, -30], ![-48, -470, 262, -159, 744], ![244, 18, 44, -56, 107]]]
  hmulB := by decide  
  f := ![![![-211, 774, -544, 316, -882]], ![![-218, 591, -412, 240, -654]], ![![-15, 696, -499, 288, -852]], ![![-311, 724, -502, 293, -786]], ![![-185, 232, -156, 92, -223]]]
  g := ![![![-9, 10, 8, -12, 18], ![-20, 135, -68, 40, -198], ![57, -114, -19, 60, -30], ![49, -470, 262, -159, 744], ![-33, 18, 44, -56, 107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-415, -201, -556, 30, -731]] ![![-59507, 12297, -5442, 3774, 4979]]
  ![![-211, 774, -544, 316, -882]] where
 M := ![![![-211, 774, -544, 316, -882]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-211, 774, -544, 316, -882]] ![![61, 10, 8, -12, 18]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 38, -10, 0, -32]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![53, 38, -10, 0, -32]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![15, 14, 35, 1, 0], ![40, 23, 3, 0, 1]] where
  M :=![![![53, 38, -10, 0, -32], ![-64, 75, -58, 44, -160], ![-320, -270, 79, -16, 256], ![288, -230, 190, -159, 528], ![232, 142, -30, -8, -103]]]
  hmulB := by decide  
  f := ![![![-33, -18, 14, -8, 32]], ![![64, 5, -10, 4, -32]], ![![-64, 58, -47, 24, -64]], ![![-45, 40, -35, 17, -48]], ![![0, -11, 5, -4, 9]]]
  g := ![![![31, 18, 2, 0, -32], ![132, 73, -26, 44, -160], ![-240, -138, -3, -16, 256], ![-429, -236, 97, -159, 528], ![104, 61, 13, -8, -103]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [30, 16, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 6, 40], [32, 36, 3], [0, 1]]
 g := ![![[22, 5, 21], [24, 27, 38], [37, 16], [15, 17, 1], []], ![[12, 34, 23, 1], [38, 6, 19, 1], [30, 1], [25, 11, 31, 25], [31, 9]], ![[4, 12, 32, 26], [36, 16, 12, 3], [35, 25], [41, 10, 36, 22], [25, 9]]]
 h' := ![![[28, 6, 40], [11, 21, 8], [21, 32, 34], [23, 24, 39], [0, 0, 1], [0, 1]], ![[32, 36, 3], [33, 40, 10], [38, 20, 10], [32, 15, 42], [26, 0, 36], [28, 6, 40]], ![[0, 1], [37, 25, 25], [41, 34, 42], [39, 4, 5], [16, 0, 6], [32, 36, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 4], []]
 b := ![[], [34, 1, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [30, 16, 26, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11093131, -3744466, -13542303, 1726253, -19103695]
  a := ![13, 62, -101, 45, -211]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16910718, 9569139, -387211, 1726253, -19103695]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -18, 14, -8, 32]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-33, -18, 14, -8, 32]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![14, 16, 1, 0, 0], ![17, 30, 0, 1, 0], ![28, 8, 0, 0, 1]] where
  M :=![![![-33, -18, 14, -8, 32], ![64, 5, -10, 4, -32], ![-64, 58, -47, 24, -64], ![-96, -110, 70, -45, 144], ![40, -42, 26, -16, 35]]]
  hmulB := by decide  
  f := ![![![53, 38, -10, 0, -32]], ![![-64, 75, -58, 44, -160]], ![![-14, 34, -23, 16, -64]], ![![-17, 62, -40, 27, -112]], ![![28, 42, -18, 8, -53]]]
  g := ![![![-23, -6, 14, -8, 32], ![24, 7, -10, 4, -32], ![46, 14, -47, 24, -64], ![-101, -24, 70, -45, 144], ![-24, -6, 26, -16, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [14, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 42], [0, 1]]
 g := ![![[35, 40], [18, 17], [41], [35, 31], [1]], ![[0, 3], [30, 26], [41], [24, 12], [1]]]
 h' := ![![[26, 42], [6, 13], [16, 19], [26, 27], [29, 26], [0, 1]], ![[0, 1], [0, 30], [37, 24], [40, 16], [17, 17], [26, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [11, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [14, 17, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![550, 518, 2475, -66, 3371]
  a := ![-1, 4, -12, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2962, -1490, 2475, -66, 3371]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![53, 38, -10, 0, -32]] ![![-33, -18, 14, -8, 32]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3131, -1195, -3924, 346, -5389]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-3131, -1195, -3924, 346, -5389]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![7, 34, 25, 4, 1]] where
  M :=![![![-3131, -1195, -3924, 346, -5389], ![-10778, -4088, -13556, 1200, -18641], ![-37282, -14093, -46811, 4170, -64405], ![-59016, -22395, -73941, 6569, -101652], ![-6822, -2619, -8532, 748, -11704]]]
  hmulB := by decide  
  f := ![![![3, -53, 38, -22, 65]], ![![130, 130, -100, 56, -203]], ![![-406, -159, 137, -74, 329]], ![![264, -105, 57, -35, 36]], ![![-93, -5, 9, -4, 36]]]
  g := ![![![736, 3873, 2783, 466, -5389], ![2547, 13398, 9627, 1612, -18641], ![8799, 46291, 33262, 5570, -64405], ![13884, 73059, 52497, 8791, -101652], ![1598, 8411, 6044, 1012, -11704]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [40, 8, 34, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 20, 5, 3], [11, 19, 11, 21], [38, 7, 31, 23], [0, 1]]
 g := ![![[15, 13, 12, 2], [46, 31, 14, 21], [1, 14, 40, 36], [13, 1], []], ![[5, 19, 40, 4, 33, 27], [36, 43, 43, 25, 20, 28], [12, 26, 6, 33, 17, 21], [24, 45, 43, 21, 33, 4], [11, 6, 9]], ![[42, 34, 38, 30, 33, 27], [17, 24, 14, 21, 19, 42], [42, 16, 23, 30, 17, 16], [8, 13, 17, 28, 43, 24], [2, 38, 18]], ![[18, 4, 9, 43, 46, 39], [0, 12, 28, 30, 21, 39], [26, 0, 32, 25, 0, 41], [40, 6, 26, 7, 38, 38], [9, 31, 12]]]
 h' := ![![[11, 20, 5, 3], [40, 39, 1, 40], [7, 5, 11, 16], [44, 44, 20, 41], [0, 0, 1], [0, 1]], ![[11, 19, 11, 21], [28, 17, 28, 44], [1, 42, 36, 42], [46, 20, 40, 17], [10, 18, 10, 39], [11, 20, 5, 3]], ![[38, 7, 31, 23], [13, 46, 34, 14], [4, 17, 34, 40], [29, 2, 10, 12], [41, 10, 28, 34], [11, 19, 11, 21]], ![[0, 1], [22, 39, 31, 43], [33, 30, 13, 43], [11, 28, 24, 24], [3, 19, 8, 21], [38, 7, 31, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [39, 17, 33], []]
 b := ![[], [], [42, 12, 23, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [40, 8, 34, 34, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10442137, 7790588, 12576268, 39517, 14211928]
  a := ![3, -18, 28, -15, 56]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1894497, -10115212, -7291956, -1208685, 14211928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -53, 38, -22, 65]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![3, -53, 38, -22, 65]] 
 ![![47, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![3, -53, 38, -22, 65], ![130, 130, -100, 56, -203], ![-406, -159, 137, -74, 329], ![264, -105, 57, -35, 36], ![282, 111, -96, 52, -230]]]
  hmulB := by decide  
  f := ![![![-3131, -1195, -3924, 346, -5389]], ![![-2894, -1104, -3628, 320, -4983]], ![![-3791, -1444, -4753, 420, -6530]], ![![-2588, -985, -3243, 287, -4456]], ![![-345, -132, -432, 38, -593]]]
  g := ![![![14, -53, 38, -22, 65], ![-23, 130, -100, 56, -203], ![6, -159, 137, -74, 329], ![53, -105, 57, -35, 36], ![-4, 111, -96, 52, -230]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-3131, -1195, -3924, 346, -5389]] ![![3, -53, 38, -22, 65]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5683, -4855, -611, -324, 1698]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-5683, -4855, -611, -324, 1698]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![47, 3, 34, 1, 0], ![29, 46, 35, 0, 1]] where
  M :=![![![-5683, -4855, -611, -324, 1698], ![3396, -5724, -3325, -2998, 714], ![1428, 20343, -36560, 6912, -68382], ![-70080, -4705, -52723, 16041, -88368], ![-21628, -18087, 913, -1072, 10771]]]
  hmulB := by decide  
  f := ![![![229369, 96273, -82391, 45002, -196410]], ![![-392820, 28374, 2065, 3028, 97998]], ![![195996, -509949, 355676, -207006, 562662]], ![![321223, -226858, 144835, -86887, 171072]], ![![-88647, -252769, 186932, -106738, 341803]]]
  g := ![![![-749, -1547, -925, -324, 1698], ![2332, -558, 1389, -2998, 714], ![31314, 59343, 40034, 6912, -68382], ![32805, 75700, 47071, 16041, -88368], ![-5351, -9629, -6408, -1072, 10771]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [2, 23, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 43, 4], [29, 9, 49], [0, 1]]
 g := ![![[4], [23, 11], [34, 44, 13], [27, 17], [1]], ![[22, 37, 11, 44], [13, 29], [19, 6, 50, 16], [39, 28], [11, 51, 16, 11]], ![[3, 11, 9, 9], [51, 42], [26, 40, 43, 10], [24, 38], [47, 18, 42, 42]]]
 h' := ![![[45, 43, 4], [20, 51], [38, 40, 8], [3, 20, 38], [51, 30, 21], [0, 1]], ![[29, 9, 49], [36, 20, 45], [3, 1, 20], [44, 22, 51], [49, 4, 44], [45, 43, 4]], ![[0, 1], [15, 35, 8], [45, 12, 25], [22, 11, 17], [21, 19, 41], [29, 9, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 35], []]
 b := ![[], [17, 20, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [2, 23, 32, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6856208, 2146582, 7228095, -974748, 10231779]
  a := ![1, -48, 78, -35, 163]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4604759, -8784736, -5995146, -974748, 10231779]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-229369, -96273, 82391, -45002, 196410]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-229369, -96273, 82391, -45002, 196410]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![8, 38, 1, 0, 0], ![7, 51, 0, 1, 0], ![36, 3, 0, 0, 1]] where
  M :=![![![-229369, -96273, 82391, -45002, 196410], ![392820, -28374, -2065, -3028, -97998], ![-195996, 509949, -355676, 207006, -562662], ![-759072, -704839, 550547, -309015, 1126416], ![140132, -354337, 246915, -143750, 389629]]]
  hmulB := by decide  
  f := ![![![5683, 4855, 611, 324, -1698]], ![![-3396, 5724, 3325, 2998, -714]], ![![-1604, 4453, 3166, 2068, 522]], ![![-1195, 6238, 4275, 2625, 756]], ![![4076, 3963, 586, 410, -1397]]]
  g := ![![![-144231, -28703, 82391, -45002, 196410], ![74688, 9406, -2065, -3028, -97998], ![404834, 97289, -355676, 207006, -562662], ![-821723, -174436, 550547, -309015, 1126416], ![-280294, -67448, 246915, -143750, 389629]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [48, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 52], [0, 1]]
 g := ![![[19, 9], [40], [45, 42], [29], [42, 1]], ![[26, 44], [40], [7, 11], [29], [31, 52]]]
 h' := ![![[42, 52], [51, 50], [13, 27], [43, 25], [51, 20], [0, 1]], ![[0, 1], [31, 3], [34, 26], [33, 28], [43, 33], [42, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [33, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [48, 11, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![140, 167, -141, 94, -304]
  a := ![4, 3, -4, 3, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![218, 31, -141, 94, -304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-5683, -4855, -611, -324, 1698]] ![![-229369, -96273, 82391, -45002, 196410]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![123, 46, 135, -14, 185]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![123, 46, 135, -14, 185]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![9, 46, 20, 1, 0], ![9, 42, 15, 0, 1]] where
  M :=![![![123, 46, 135, -14, 185], ![370, 171, 447, -30, 589], ![1178, 438, 1608, -134, 2225], ![2040, 664, 2596, -267, 3660], ![298, 106, 297, -36, 410]]]
  hmulB := by decide  
  f := ![![![97, 110, -85, 48, -169]], ![![-338, -155, 131, -72, 307]], ![![614, -10, -26, 8, -193]], ![![-41, -100, 75, -43, 139]], ![![-77, -96, 74, -42, 146]]]
  g := ![![![-24, -120, -40, -14, 185], ![-79, -393, -132, -30, 589], ![-299, -1472, -493, -134, 2225], ![-483, -2386, -796, -267, 3660], ![-52, -262, -87, -36, 410]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [24, 58, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 43, 33], [28, 15, 26], [0, 1]]
 g := ![![[35, 11, 27], [44, 57, 53], [58, 45], [42, 58, 19], [1]], ![[21, 19, 24, 31], [52, 18, 33, 18], [7, 3], [50, 17, 30, 24], [11, 50, 27, 6]], ![[40, 39, 15, 16], [21, 20, 16, 12], [34, 45], [24, 58, 4, 20], [41, 10, 10, 53]]]
 h' := ![![[45, 43, 33], [6, 15, 33], [49, 51, 17], [54, 52, 24], [35, 1, 14], [0, 1]], ![[28, 15, 26], [27, 50, 46], [44, 11, 50], [25, 44, 11], [1, 23, 7], [45, 43, 33]], ![[0, 1], [3, 53, 39], [4, 56, 51], [17, 22, 24], [23, 35, 38], [28, 15, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 56], []]
 b := ![[], [23, 42, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [24, 58, 45, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10778138, -4451564, -13454214, 1057858, -18192404]
  a := ![7, 22, -51, 7, -98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2431064, 12050304, 4038554, 1057858, -18192404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2011, 2189, -1690, 952, -3381]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![2011, 2189, -1690, 952, -3381]] 
 ![![59, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![2011, 2189, -1690, 952, -3381], ![-6762, -2962, 2518, -1378, 5943], ![11886, -541, -291, 40, -3357], ![24, 8817, -6345, 3655, -10884], ![-8322, 345, 228, -42, 2392]]]
  hmulB := by decide  
  f := ![![![617, 2783, -1516, 856, -4275]], ![![-124, 50, -62, 50, -159]], ![![547, 2306, -1269, 700, -3552]], ![![537, 348, -105, -11, -303]], ![![278, 1145, -616, 346, -1742]]]
  g := ![![![2633, 2189, -1690, 952, -3381], ![-4306, -2962, 2518, -1378, 5943], ![1627, -541, -291, 40, -3357], ![9120, 8817, -6345, 3655, -10884], ![-1174, 345, 228, -42, 2392]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -45, 3, 10, 16]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-103, -45, 3, 10, 16]] 
 ![![59, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-103, -45, 3, 10, 16], ![32, -186, 113, -76, 320], ![640, 357, -62, -34, -224], ![-240, 613, -401, 285, -1128], ![-428, -153, -7, 54, 11]]]
  hmulB := by decide  
  f := ![![![-1005, -347, 317, -168, 784]], ![![-263, -105, 94, -50, 224]], ![![-106, 7, 4, 0, 32]], ![![-555, -220, 198, -105, 472]], ![![4, -29, 21, -12, 35]]]
  g := ![![![6, -45, 3, 10, 16], ![80, -186, 113, -76, 320], ![-69, 357, -62, -34, -224], ![-280, 613, -401, 285, -1128], ![11, -153, -7, 54, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![123, 46, 135, -14, 185]] ![![2011, 2189, -1690, 952, -3381]]
  ![![1005, 347, -317, 168, -784]] where
 M := ![![![1005, 347, -317, 168, -784]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![1005, 347, -317, 168, -784]] ![![-103, -45, 3, 10, 16]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5727, -3225, 2648, -1464, 5917]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-5727, -3225, 2648, -1464, 5917]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![32, 54, 1, 0, 0], ![51, 53, 0, 1, 0], ![60, 29, 0, 0, 1]] where
  M :=![![![-5727, -3225, 2648, -1464, 5917], ![11834, 1252, -1578, 782, -5551], ![-11102, 10333, -6799, 4036, -8987], ![-14904, -19209, 14673, -8293, 28740], ![7830, -7161, 4704, -2794, 6182]]]
  hmulB := by decide  
  f := ![![![949, 427, -82, -88, -235]], ![![-470, 1718, -1246, 746, -3287]], ![![-26, 1685, -1145, 620, -3009]], ![![413, 1750, -1103, 531, -2896]], ![![776, 1261, -674, 260, -1799]]]
  g := ![![![-6079, -3938, 2648, -1464, 5917], ![5828, 3377, -1578, 782, -5551], ![8850, 6954, -6799, 4036, -8987], ![-29277, -19762, 14673, -8293, 28740], ![-6084, -4793, 4704, -2794, 6182]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [46, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 60], [0, 1]]
 g := ![![[30, 4], [5], [57, 57], [53, 25], [23, 1]], ![[0, 57], [5], [26, 4], [18, 36], [46, 60]]]
 h' := ![![[23, 60], [15, 2], [1, 35], [2, 22], [40, 56], [0, 1]], ![[0, 1], [0, 59], [13, 26], [20, 39], [47, 5], [23, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [57, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [46, 38, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![349, 238, 79, 44, -30]
  a := ![1, 4, -8, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-43, -90, 79, 44, -30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-653, -781, 599, -338, 1184]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-653, -781, 599, -338, 1184]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![17, 0, 1, 0, 0], ![0, 9, 0, 1, 0], ![57, 27, 0, 0, 1]] where
  M :=![![![-653, -781, 599, -338, 1184], ![2368, 1128, -947, 520, -2192], ![-4384, -27, 272, -110, 1520], ![336, -2995, 2135, -1233, 3576], ![3068, 31, -199, 82, -1079]]]
  hmulB := by decide  
  f := ![![![3951, 1499, 4935, -440, 6784]], ![![13568, 5182, 17011, -1498, 23360]], ![![1867, 708, 2339, -208, 3216]], ![![3216, 1223, 4034, -357, 5544]], ![![9839, 3748, 12317, -1090, 16921]]]
  g := ![![![-1284, -487, 599, -338, 1184], ![2351, 912, -947, 520, -2192], ![-1568, -657, 272, -110, 1520], ![-3931, -1450, 2135, -1233, 3576], ![1114, 466, -199, 82, -1079]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [5, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 60], [0, 1]]
 g := ![![[44, 49], [46], [12, 42], [53, 57], [24, 1]], ![[0, 12], [46], [44, 19], [18, 4], [48, 60]]]
 h' := ![![[24, 60], [15, 7], [1, 31], [40, 15], [2, 22], [0, 1]], ![[0, 1], [0, 54], [13, 30], [34, 46], [42, 39], [24, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [47, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [5, 37, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2909, 525, 11367, -610, 17296]
  a := ![3, -11, 27, -1, 56]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19282, -7557, 11367, -610, 17296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7339, -335, 661, -302, 2898]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-7339, -335, 661, -302, 2898]] 
 ![![61, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-7339, -335, 661, -302, 2898], ![5796, -7462, 5037, -2964, 7242], ![14484, 24339, -18340, 10410, -34926], ![-37824, -17169, 14517, -7957, 33984], ![-9996, -16975, 12785, -7258, 24323]]]
  hmulB := by decide  
  f := ![![![-4231, -2263, -4063, 236, -4986]], ![![-649, -341, -706, 38, -888]], ![![-1464, -609, -1708, 144, -2298]], ![![-4426, -2119, -4465, 337, -5724]], ![![-3023, -1630, -2866, 164, -3499]]]
  g := ![![![-1932, -335, 661, -302, 2898], ![-2672, -7462, 5037, -2964, 7242], ![16677, 24339, -18340, 10410, -34926], ![-18347, -17169, 14517, -7957, 33984], ![-11606, -16975, 12785, -7258, 24323]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-5727, -3225, 2648, -1464, 5917]] ![![-653, -781, 599, -338, 1184]]
  ![![2155551, 5331598, -3959265, 2257752, -7306315]] where
 M := ![![![2155551, 5331598, -3959265, 2257752, -7306315]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![2155551, 5331598, -3959265, 2257752, -7306315]] ![![-7339, -335, 661, -302, 2898]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-54626927949, -51609691659, 40257546946, -22605479918, 82155453127]]]
 hmul := by decide  
 g := ![![![![-895523409, -846060519, 659959786, -370581638, 1346810707]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB251I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB251I1 : PrimesBelowBoundCertificateInterval O 23 61 251 where
  m := 9
  g := ![1, 1, 2, 3, 2, 2, 2, 3, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB251I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20511149]
    · exact ![28629151]
    · exact ![50653, 1369]
    · exact ![68921, 41, 41]
    · exact ![79507, 1849]
    · exact ![4879681, 47]
    · exact ![148877, 2809]
    · exact ![205379, 59, 59]
    · exact ![3721, 3721, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I41N1, I41N2, I47N1, I59N1, I59N2, I61N2]
  Il := ![[], [], [], [I41N1, I41N2], [], [I47N1], [], [I59N1, I59N2], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
