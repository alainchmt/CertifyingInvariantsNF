
import IdealArithmetic.Examples.NF3_1_996008_1.RI3_1_996008_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![14, -61, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![14, -61, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![14, 202, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![14, -61, 1], ![198, 39, -61], ![-12078, -1327, 39]]]
  hmulB := by decide  
  f := ![![![-13, 61, -1], ![263, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -202, 263]], ![![0, -1, 1], ![4, 47, -61], ![-48, -35, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [12, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [191, 262], [0, 1]]
 g := ![![[6, 22], [240, 200], [64, 128], [70], [22], [70], [187], [1]], ![[0, 241], [42, 63], [53, 135], [70], [22], [70], [187], [1]]]
 h' := ![![[191, 262], [13, 223], [21, 48], [77, 91], [172, 164], [228, 223], [4, 99], [251, 191], [0, 1]], ![[0, 1], [0, 40], [247, 215], [100, 172], [199, 99], [215, 40], [240, 164], [175, 72], [191, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [43, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [12, 72, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![408, 176, -46]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 36, -46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![61, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![61, 1, 0]] 
 ![![263, 0, 0], ![61, 1, 0], ![224, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![61, 1, 0], ![0, 61, 1], ![198, 25, 61]]]
  hmulB := by decide  
  f := ![![![3722, 61, 0], ![-16043, 0, 0]], ![![854, 14, 0], ![-3681, 0, 0]], ![![3126, 51, 0], ![-13474, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 263, 0], ![-224, 0, 263]], ![![0, 1, 0], ![-15, 61, 1], ![-57, 25, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![14, -61, 1]] ![![263, 0, 0], ![61, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![16043, 263, 0]], ![![3682, -16043, 263], ![1052, -3682, 0]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![61, 1, 0]]], ![![![14, -61, 1]], ![![4, -14, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0]] 
 ![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [248, 184, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [156, 231, 146], [260, 37, 123], [0, 1]]
 g := ![![[238, 204, 25], [236, 11], [25, 252, 4], [58, 125, 99], [23, 239], [156, 148], [147, 1], []], ![[69, 47, 235, 266], [202, 66], [68, 189, 151, 101], [14, 13, 37, 194], [61, 199], [192, 1], [18, 24], [73, 65]], ![[220, 22, 259, 19], [67, 208], [155, 172, 215, 266], [198, 103, 38, 181], [57, 105], [169, 228], [50, 99], [96, 65]]]
 h' := ![![[156, 231, 146], [14, 164, 5], [256, 143, 77], [142, 84, 267], [205, 65, 38], [23, 265, 152], [128, 142, 174], [0, 0, 1], [0, 1]], ![[260, 37, 123], [268, 45, 188], [205, 256, 55], [244, 0, 85], [219, 97, 136], [52, 198, 198], [251, 157, 1], [45, 18, 37], [156, 231, 146]], ![[0, 1], [146, 60, 76], [114, 139, 137], [34, 185, 186], [220, 107, 95], [38, 75, 188], [40, 239, 94], [214, 251, 231], [260, 37, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [259, 249], []]
 b := ![[], [228, 73, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [248, 184, 122, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![507065, 416950, 34163]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1885, 1550, 127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def PBC269 : ContainsPrimesAboveP 269 ![I269N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![269, 0, 0]]) timesTableT_eq_Table B_one_repr 269 (by decide) 𝕀

instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-152, -12, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-152, -12, 1]] 
 ![![271, 0, 0], ![0, 271, 0], ![119, 259, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-152, -12, 1], ![198, -127, -12], ![-2376, -102, -127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -259, 271]], ![![-1, -1, 1], ![6, 11, -12], ![47, 121, -127]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [137, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [249, 270], [0, 1]]
 g := ![![[105, 74], [58, 122], [109, 138], [268, 99], [229], [169], [213], [1]], ![[103, 197], [84, 149], [54, 133], [258, 172], [229], [169], [213], [1]]]
 h' := ![![[249, 270], [184, 138], [243, 193], [140, 229], [161, 218], [141, 59], [157, 258], [134, 249], [0, 1]], ![[0, 1], [129, 133], [62, 78], [251, 42], [243, 53], [198, 212], [172, 13], [76, 22], [249, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [229, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [137, 22, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2429, 42, 132]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49, -126, 132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![12, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![12, 1, 0]] 
 ![![271, 0, 0], ![12, 1, 0], ![127, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![12, 1, 0], ![0, 12, 1], ![198, 25, 12]]]
  hmulB := by decide  
  f := ![![![1285, 107, 0], ![-28997, 0, 0]], ![![36, 3, 0], ![-812, 0, 0]], ![![589, 49, 0], ![-13291, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 271, 0], ![-127, 0, 271]], ![![0, 1, 0], ![-1, 12, 1], ![-6, 25, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![-152, -12, 1]] ![![271, 0, 0], ![12, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![3252, 271, 0]], ![![-41192, -3252, 271], ![-1626, -271, 0]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![12, 1, 0]]], ![![![-152, -12, 1]], ![![-6, -1, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![277, 0, 0]] 
 ![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]] where
  M :=![![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [92, 160, 147, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [189, 187, 127], [218, 89, 150], [0, 1]]
 g := ![![[13, 96, 106], [184, 84], [234, 141, 243], [224, 157], [223, 201, 69], [208, 273], [130, 1], []], ![[230, 64, 73, 46], [173, 21], [63, 139, 0, 149], [144, 214], [242, 10, 228, 115], [78, 22], [202, 165], [11, 63]], ![[210, 43, 54, 224], [196, 21], [104, 258, 98, 126], [255, 76], [211, 98, 62, 68], [76, 75], [152, 67], [265, 63]]]
 h' := ![![[189, 187, 127], [236, 54, 99], [78, 93, 258], [214, 28, 215], [259, 49, 218], [162, 160, 247], [228, 160, 120], [0, 0, 1], [0, 1]], ![[218, 89, 150], [199, 45, 157], [270, 157, 148], [21, 200, 254], [132, 171, 141], [182, 230, 199], [106, 208, 253], [84, 251, 89], [189, 187, 127]], ![[0, 1], [9, 178, 21], [271, 27, 148], [156, 49, 85], [252, 57, 195], [259, 164, 108], [7, 186, 181], [153, 26, 187], [218, 89, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140, 2], []]
 b := ![[], [11, 261, 229], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [92, 160, 147, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1102460, -6925, 20775]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3980, -25, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def PBC277 : ContainsPrimesAboveP 277 ![I277N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![277, 0, 0]]) timesTableT_eq_Table B_one_repr 277 (by decide) 𝕀

instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0], ![47, 1, 0]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![281, 0, 0], ![47, 1, 0]] 
 ![![281, 0, 0], ![47, 1, 0], ![39, 0, 1]] where
  M :=![![![281, 0, 0], ![0, 281, 0], ![0, 0, 281]], ![![47, 1, 0], ![0, 47, 1], ![198, 25, 47]]]
  hmulB := by decide  
  f := ![![![189, 4, 0], ![-1124, 0, 0]], ![![-47, -1, 0], ![282, 0, 0]], ![![-39, -1, 0], ![234, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 281, 0], ![-39, 0, 281]], ![![0, 1, 0], ![-8, 47, 1], ![-10, 25, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N0 : Nat.card (O ⧸ I281N0) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N0)

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := prime_ideal_of_norm_prime hp281.out _ NI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0], ![48, 1, 0]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![281, 0, 0], ![48, 1, 0]] 
 ![![281, 0, 0], ![48, 1, 0], ![225, 0, 1]] where
  M :=![![![281, 0, 0], ![0, 281, 0], ![0, 0, 281]], ![![48, 1, 0], ![0, 48, 1], ![198, 25, 48]]]
  hmulB := by decide  
  f := ![![![1873, 39, 0], ![-10959, 0, 0]], ![![240, 5, 0], ![-1404, 0, 0]], ![![1497, 31, 0], ![-8759, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 281, 0], ![-225, 0, 281]], ![![0, 1, 0], ![-9, 48, 1], ![-42, 25, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0], ![-95, 1, 0]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![281, 0, 0], ![-95, 1, 0]] 
 ![![281, 0, 0], ![186, 1, 0], ![248, 0, 1]] where
  M :=![![![281, 0, 0], ![0, 281, 0], ![0, 0, 281]], ![![-95, 1, 0], ![0, -95, 1], ![198, 25, -95]]]
  hmulB := by decide  
  f := ![![![9976, -105, 0], ![29505, 0, 0]], ![![6556, -69, 0], ![19390, 0, 0]], ![![8678, -91, 0], ![25666, 1, 0]]]
  g := ![![![1, 0, 0], ![-186, 281, 0], ![-248, 0, 281]], ![![-1, 1, 0], ![62, -95, 1], ![68, 25, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![281, 0, 0], ![47, 1, 0]] ![![281, 0, 0], ![48, 1, 0]]
  ![![281, 0, 0], ![8, 95, 1]] where
 M := ![![![78961, 0, 0], ![13488, 281, 0]], ![![13207, 281, 0], ![2256, 95, 1]]]
 hmul := by decide  
 g := ![![![![273, -95, -1], ![281, 0, 0]], ![![40, -94, -1], ![281, 0, 0]]], ![![![39, -94, -1], ![281, 0, 0]], ![![8, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![281, 0, 0], ![8, 95, 1]] ![![281, 0, 0], ![-95, 1, 0]]
  ![![281, 0, 0]] where
 M := ![![![78961, 0, 0], ![-26695, 281, 0]], ![![2248, 26695, 281], ![-562, -8992, 0]]]
 hmul := by decide  
 g := ![![![![281, 0, 0]], ![![-95, 1, 0]]], ![![![8, 95, 1]], ![![-2, -32, 0]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1, I281N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
    exact isPrimeI281N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0 ⊙ MulI281N1)


lemma PB283I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271, 277, 281] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 282 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 282 (by omega)

def PB283I5 : PrimesBelowBoundCertificateInterval O 257 282 283 where
  m := 5
  g := ![2, 1, 2, 1, 3]
  P := ![263, 269, 271, 277, 281]
  hP := PB283I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0]
    · exact ![I271N0, I271N1]
    · exact ![I277N0]
    · exact ![I281N0, I281N1, I281N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![69169, 263]
    · exact ![19465109]
    · exact ![73441, 271]
    · exact ![21253933]
    · exact ![281, 281, 281]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
      exact NI281N2
  β := ![I263N1, I271N1, I281N0, I281N1, I281N2]
  Il := ![[I263N1], [], [I271N1], [], [I281N0, I281N1, I281N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
