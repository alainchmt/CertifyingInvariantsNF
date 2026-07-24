
import IdealArithmetic.Examples.NF3_1_959175_1.RI3_1_959175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![34, 1, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![34, 1, 0]] 
 ![![263, 0, 0], ![34, 1, 0], ![194, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![34, 1, 0], ![0, 35, 2], ![280, 52, 33]]]
  hmulB := by decide  
  f := ![![![3707, 109, 0], ![-28667, 0, 0]], ![![442, 13, 0], ![-3418, 0, 0]], ![![2774, 64, -1], ![-21452, 132, 0]]]
  g := ![![![1, 0, 0], ![-34, 263, 0], ![-194, 0, 263]], ![![0, 1, 0], ![-6, 35, 2], ![-30, 52, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N0 : Nat.card (O ⧸ I263N0) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N0)

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := prime_ideal_of_norm_prime hp263.out _ NI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![52, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![52, 1, 0]] 
 ![![263, 0, 0], ![52, 1, 0], ![200, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![52, 1, 0], ![0, 53, 2], ![280, 52, 51]]]
  hmulB := by decide  
  f := ![![![3537, 68, 0], ![-17884, 0, 0]], ![![676, 13, 0], ![-3418, 0, 0]], ![![2632, 24, -1], ![-13308, 132, 0]]]
  g := ![![![1, 0, 0], ![-52, 263, 0], ![-200, 0, 263]], ![![0, 1, 0], ![-12, 53, 2], ![-48, 52, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-86, 1, 0]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-86, 1, 0]] 
 ![![263, 0, 0], ![177, 1, 0], ![27, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-86, 1, 0], ![0, -85, 2], ![280, 52, -87]]]
  hmulB := by decide  
  f := ![![![11181, -130, 0], ![34190, 0, 0]], ![![7483, -87, 0], ![22882, 0, 0]], ![![1261, 28, -1], ![3856, 132, 0]]]
  g := ![![![1, 0, 0], ![-177, 263, 0], ![-27, 0, 263]], ![![-1, 1, 0], ![57, -85, 2], ![-25, 52, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![34, 1, 0]] ![![263, 0, 0], ![52, 1, 0]]
  ![![263, 0, 0], ![95, -88, 1]] where
 M := ![![![69169, 0, 0], ![13676, 263, 0]], ![![8942, 263, 0], ![1768, 87, 2]]]
 hmul := by decide  
 g := ![![![![168, 88, -1], ![263, 0, 0]], ![![-43, 89, -1], ![263, 0, 0]]], ![![![-61, 89, -1], ![263, 0, 0]], ![![6, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![95, -88, 1]] ![![263, 0, 0], ![-86, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-22618, 263, 0]], ![![24985, -23144, 263], ![-7890, 7627, -263]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-86, 1, 0]]], ![![![95, -88, 1]], ![![-30, 29, -1]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-131, 1, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-131, 1, 0]] 
 ![![269, 0, 0], ![138, 1, 0], ![93, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-131, 1, 0], ![0, -130, 2], ![280, 52, -132]]]
  hmulB := by decide  
  f := ![![![27380, -209, 0], ![56221, 0, 0]], ![![14018, -107, 0], ![28784, 0, 0]], ![![9464, -7, -1], ![19433, 135, 0]]]
  g := ![![![1, 0, 0], ![-138, 269, 0], ![-93, 0, 269]], ![![-1, 1, 0], ![66, -130, 2], ![20, 52, -132]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N0 : Nat.card (O ⧸ I269N0) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N0)

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := prime_ideal_of_norm_prime hp269.out _ NI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-119, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-119, 1, 0]] 
 ![![269, 0, 0], ![150, 1, 0], ![242, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-119, 1, 0], ![0, -118, 2], ![280, 52, -120]]]
  hmulB := by decide  
  f := ![![![10235, -86, 0], ![23134, 0, 0]], ![![5832, -49, 0], ![13182, 0, 0]], ![![9190, -18, -1], ![20772, 135, 0]]]
  g := ![![![1, 0, 0], ![-150, 269, 0], ![-242, 0, 269]], ![![-1, 1, 0], ![64, -118, 2], ![80, 52, -120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-19, 1, 0]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-19, 1, 0]] 
 ![![269, 0, 0], ![250, 1, 0], ![98, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-19, 1, 0], ![0, -18, 2], ![280, 52, -20]]]
  hmulB := by decide  
  f := ![![![1654, -87, 0], ![23403, 0, 0]], ![![1540, -81, 0], ![21790, 0, 0]], ![![628, -24, -1], ![8886, 135, 0]]]
  g := ![![![1, 0, 0], ![-250, 269, 0], ![-98, 0, 269]], ![![-1, 1, 0], ![16, -18, 2], ![-40, 52, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![-131, 1, 0]] ![![269, 0, 0], ![-119, 1, 0]]
  ![![269, 0, 0], ![-141, 10, 1]] where
 M := ![![![72361, 0, 0], ![-32011, 269, 0]], ![![-35239, 269, 0], ![15589, -249, 2]]]
 hmul := by decide  
 g := ![![![![269, 0, 0], ![0, 0, 0]], ![![22, -9, -1], ![269, 0, 0]]], ![![![10, -9, -1], ![269, 0, 0]], ![![59, -1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![-141, 10, 1]] ![![269, 0, 0], ![-19, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![-5111, 269, 0]], ![![-37929, 2690, 269], ![2959, -269, 0]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![-19, 1, 0]]], ![![![-141, 10, 1]], ![![11, -1, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1, I269N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0 ⊙ MulI269N1)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-89, -30, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-89, -30, 1]] 
 ![![271, 0, 0], ![0, 271, 0], ![182, 241, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-89, -30, 1], ![280, -67, -61], ![-8680, -1446, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-182, -241, 271]], ![![-1, -1, 1], ![42, 54, -61], ![-28, 0, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [229, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 270], [0, 1]]
 g := ![![[215, 200], [169, 25], [12, 11], [62, 5], [126], [212], [252], [1]], ![[0, 71], [176, 246], [156, 260], [226, 266], [126], [212], [252], [1]]]
 h' := ![![[87, 270], [52, 124], [233, 5], [165, 108], [174, 238], [64, 111], [153, 235], [42, 87], [0, 1]], ![[0, 1], [0, 147], [126, 266], [76, 163], [13, 33], [236, 160], [2, 36], [23, 184], [87, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [157, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [229, 184, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1069, 1286, -79]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57, 75, -79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![61, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![61, 1, 0]] 
 ![![271, 0, 0], ![61, 1, 0], ![6, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![61, 1, 0], ![0, 62, 2], ![280, 52, 60]]]
  hmulB := by decide  
  f := ![![![1831, 30, 0], ![-8130, 0, 0]], ![![305, 5, 0], ![-1354, 0, 0]], ![![-54, -32, -1], ![240, 136, 0]]]
  g := ![![![1, 0, 0], ![-61, 271, 0], ![-6, 0, 271]], ![![0, 1, 0], ![-14, 62, 2], ![-12, 52, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![-89, -30, 1]] ![![271, 0, 0], ![61, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![16531, 271, 0]], ![![-24119, -8130, 271], ![-5149, -1897, 0]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![61, 1, 0]]], ![![![-89, -30, 1]], ![![-19, -7, 0]]]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0], ![79, 1, 0]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![277, 0, 0], ![79, 1, 0]] 
 ![![277, 0, 0], ![79, 1, 0], ![164, 0, 1]] where
  M :=![![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]], ![![79, 1, 0], ![0, 80, 2], ![280, 52, 78]]]
  hmulB := by decide  
  f := ![![![11693, 148, 0], ![-40996, 0, 0]], ![![3239, 41, 0], ![-11356, 0, 0]], ![![6964, 48, -1], ![-24416, 139, 0]]]
  g := ![![![1, 0, 0], ![-79, 277, 0], ![-164, 0, 277]], ![![0, 1, 0], ![-24, 80, 2], ![-60, 52, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N0 : Nat.card (O ⧸ I277N0) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N0)

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := prime_ideal_of_norm_prime hp277.out _ NI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0], ![91, 1, 0]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![277, 0, 0], ![91, 1, 0]] 
 ![![277, 0, 0], ![91, 1, 0], ![246, 0, 1]] where
  M :=![![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]], ![![91, 1, 0], ![0, 92, 2], ![280, 52, 90]]]
  hmulB := by decide  
  f := ![![![7554, 83, 0], ![-22991, 0, 0]], ![![2366, 26, 0], ![-7201, 0, 0]], ![![6750, 28, -1], ![-20544, 139, 0]]]
  g := ![![![1, 0, 0], ![-91, 277, 0], ![-246, 0, 277]], ![![0, 1, 0], ![-32, 92, 2], ![-96, 52, 90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0], ![107, 1, 0]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![277, 0, 0], ![107, 1, 0]] 
 ![![277, 0, 0], ![107, 1, 0], ![39, 0, 1]] where
  M :=![![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]], ![![107, 1, 0], ![0, 108, 2], ![280, 52, 106]]]
  hmulB := by decide  
  f := ![![![21294, 199, 0], ![-55123, 0, 0]], ![![8132, 76, 0], ![-21051, 0, 0]], ![![2910, -27, -1], ![-7533, 139, 0]]]
  g := ![![![1, 0, 0], ![-107, 277, 0], ![-39, 0, 277]], ![![0, 1, 0], ![-42, 108, 2], ![-34, 52, 106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![277, 0, 0], ![79, 1, 0]] ![![277, 0, 0], ![91, 1, 0]]
  ![![277, 0, 0], ![-145, -53, 1]] where
 M := ![![![76729, 0, 0], ![25207, 277, 0]], ![![21883, 277, 0], ![7189, 171, 2]]]
 hmul := by decide  
 g := ![![![![277, 0, 0], ![0, 0, 0]], ![![91, 1, 0], ![0, 0, 0]]], ![![![79, 1, 0], ![0, 0, 0]], ![![27, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![277, 0, 0], ![-145, -53, 1]] ![![277, 0, 0], ![107, 1, 0]]
  ![![277, 0, 0]] where
 M := ![![![76729, 0, 0], ![29639, 277, 0]], ![![-40165, -14681, 277], ![-15235, -5817, 0]]]
 hmul := by decide  
 g := ![![![![277, 0, 0]], ![![107, 1, 0]]], ![![![-145, -53, 1]], ![![-55, -21, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1, I277N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
    exact isPrimeI277N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0 ⊙ MulI277N1)


lemma PB278I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271, 277] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 277 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 277 (by omega)

def PB278I5 : PrimesBelowBoundCertificateInterval O 257 277 278 where
  m := 4
  g := ![3, 3, 2, 3]
  P := ![263, 269, 271, 277]
  hP := PB278I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1, I277N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![263, 263, 263]
    · exact ![269, 269, 269]
    · exact ![73441, 271]
    · exact ![277, 277, 277]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
  β := ![I263N0, I263N1, I263N2, I269N0, I269N1, I269N2, I271N1, I277N0, I277N1, I277N2]
  Il := ![[I263N0, I263N1, I263N2], [I269N0, I269N1, I269N2], [I271N1], [I277N0, I277N1, I277N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
