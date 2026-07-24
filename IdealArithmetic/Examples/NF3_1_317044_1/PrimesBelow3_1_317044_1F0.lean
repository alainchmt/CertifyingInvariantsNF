
import IdealArithmetic.Examples.NF3_1_317044_1.RI3_1_317044_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 1, 5], ![-70, -20, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -2], ![-1, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 1, 5], ![-35, -20, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![0, 2, 5], ![-70, -20, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 1, 3], ![0, -1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-1, 2, 5], ![-25, -20, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![14, 1, 1]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, 1, 5]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-14, 0, -1], ![2, 0, 0]]], ![![![-14, 0, -1], ![2, 0, 0]], ![![-7, 0, 2], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![14, 1, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![28, 2, 2], ![-56, -4, 6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![14, 1, 1]], ![![-28, -2, 3]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![14, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![14, -1, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![2, 2, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![14, -1, 1], ![-70, -7, -5], ![84, 6, -6]]]
  hmulB := by decide  
  f := ![![![-13, 1, -1], ![3, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-4, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -2, 3]], ![![4, -1, 1], ![-20, 1, -5], ![32, 6, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]], ![[0, 2]]]
 h' := ![![[0, 2], [0, 1]], ![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1385, -1850, -1600]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![605, 450, -1600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![0, 0, 5], ![-70, -20, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, 2], ![0, -1, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![0, 0, 5], ![-10, -20, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![14, -1, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![42, -3, 3], ![-84, -6, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![14, -1, 1]], ![![-28, -2, -2]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1931, 480, -173]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![1931, 480, -173]] 
 ![![5, 0, 0], ![0, 1, 0], ![3, 0, 1]] where
  M :=![![![1931, 480, -173], ![12110, 5871, 2400], ![-36022, -7178, 5391]]]
  hmulB := by decide  
  f := ![![![48877761, -1345886, 2167683]], ![![-30347562, 835643, -1345886]], ![![54238573, -1493500, 2405430]]]
  g := ![![![490, 480, -173], ![982, 5871, 2400], ![-10439, -7178, 5391]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![843881, 550902, 339963]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![843881, 550902, 339963]] 
 ![![5, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![843881, 550902, 339963], ![-23797410, -5404477, 2754510], ![-33803658, -15777522, -5955379]]]
  hmulB := by decide  
  f := ![![![75645050956003, -2082943509828, 3354787282371]], ![![-46967021953194, 1293272359751, -2082943509828]], ![![68812633910632, -1894807755258, 3051775974665]]]
  g := ![![![32791, 550902, 339963], ![-5861286, -5404477, 2754510], ![-4378580, -15777522, -5955379]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3349962553761, -476912135644, 733569144734]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![-3349962553761, -476912135644, 733569144734]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![-3349962553761, -476912135644, 733569144734], ![-51349840131380, -18498257584085, -2384560678220], ![43653817521356, -731725313396, -18021345448441]]]
  hmulB := by decide  
  f := ![![![-331618646707457115778226365, 9131369457322398033387668, -14706976920649067816432070]], ![![-59397240476878743192532112, 1635547798427246143470675, -2634212079196856219757988]], ![![-169018707780330962353437148, 4654057548527797752459124, -7495821658895151889916993]]]
  g := ![![![-288462802237, -476912135644, 733569144734], ![4528638040992, -18498257584085, -2384560678220], ![9316143754988, -731725313396, -18021345448441]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![1931, 480, -173]] ![![843881, 550902, 339963]]
  ![![-3945189755, 1199154108, 3008913920]] where
 M := ![![![-3945189755, 1199154108, 3008913920]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-3945189755, 1199154108, 3008913920]] ![![-3349962553761, -476912135644, 733569144734]]
  ![![5, 0, 0]] where
 M := ![![![82990445409191912885035, -22502451182313390916280, -59978202384394235326650]]]
 hmul := by decide  
 g := ![![![![16598089081838382577007, -4500490236462678183256, -11995640476878847065330]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 1, 5], ![-70, -20, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -2], ![-3, 3, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 1, 5], ![-10, -20, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![3, 1, 0]] 
 ![![7, 0, 0], ![3, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![3, 1, 0], ![0, 4, 5], ![-70, -20, 3]]]
  hmulB := by decide  
  f := ![![![10, 3, 0], ![-21, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![6, 0, -2], ![-12, 3, 0]]]
  g := ![![![1, 0, 0], ![-3, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-6, 4, 5], ![-4, -20, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![3, 1, 0]]
  ![![7, 0, 0], ![14, -2, 1]] where
 M := ![![![49, 0, 0], ![21, 7, 0]], ![![0, 7, 0], ![0, 4, 5]]]
 hmul := by decide  
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![-11, 3, -1], ![7, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-10, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![14, -2, 1]] ![![7, 0, 0], ![3, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![21, 7, 0]], ![![98, -14, 7], ![-28, -14, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![3, 1, 0]]], ![![![14, -2, 1]], ![![-4, -2, -1]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [3, 5, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 3, 3], [9, 7, 8], [0, 1]]
 g := ![![[9, 6, 1], [0, 4, 1], []], ![[10, 6, 1, 3], [10, 9, 3, 4], [10, 9]], ![[1, 7], [3, 0, 9, 6], [5, 9]]]
 h' := ![![[6, 3, 3], [0, 10, 10], [0, 0, 1], [0, 1]], ![[9, 7, 8], [10, 5, 1], [6, 3, 7], [6, 3, 3]], ![[0, 1], [2, 7], [0, 8, 3], [9, 7, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9], []]
 b := ![[], [3, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [3, 5, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![444378, 245025, 125675]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40398, 22275, 11425]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![4, 1, 0]] 
 ![![13, 0, 0], ![4, 1, 0], ![9, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![4, 1, 0], ![0, 5, 5], ![-70, -20, 4]]]
  hmulB := by decide  
  f := ![![![17, 4, 0], ![-52, 0, 0]], ![![4, 1, 0], ![-12, 0, 0]], ![![13, 0, -3], ![-40, 8, 0]]]
  g := ![![![1, 0, 0], ![-4, 13, 0], ![-9, 0, 13]], ![![0, 1, 0], ![-5, 5, 5], ![-2, -20, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![13, 0, 0], ![11, -6, 1]] where
 M := ![![![169, 0, 0], ![52, 13, 0]], ![![52, 13, 0], ![16, 9, 5]]]
 hmul := by decide  
 g := ![![![![2, 6, -1], ![13, 0, 0]], ![![-7, 7, -1], ![13, 0, 0]]], ![![![-7, 7, -1], ![13, 0, 0]], ![![-3, 3, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![11, -6, 1]] ![![13, 0, 0], ![4, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![52, 13, 0]], ![![143, -78, 13], ![-26, -39, -26]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![4, 1, 0]]], ![![![11, -6, 1]], ![![-2, -3, -2]]]]
 hle2 := by decide  

def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![21, 5, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![21, 5, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![4, 5, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![21, 5, 1], ![-70, 6, 25], ![-336, -114, 1]]]
  hmulB := by decide  
  f := ![![![-20, -5, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -5, 17]], ![![1, 0, 1], ![-10, -7, 25], ![-20, -7, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [12, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 16], [0, 1]]
 g := ![![[3, 13], [2], [4], [1]], ![[11, 4], [2], [4], [1]]]
 h' := ![![[15, 16], [12, 9], [11, 6], [5, 15], [0, 1]], ![[0, 1], [11, 8], [16, 11], [9, 2], [15, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [7, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [12, 2, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3994, -14, 106]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![210, -32, 106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-8, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-8, 1, 0]] 
 ![![17, 0, 0], ![9, 1, 0], ![16, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-8, 1, 0], ![0, -7, 5], ![-70, -20, -8]]]
  hmulB := by decide  
  f := ![![![9, 69, -50], ![17, 170, 0]], ![![9, 34, -25], ![18, 85, 0]], ![![8, 65, -47], ![15, 160, 0]]]
  g := ![![![1, 0, 0], ![-9, 17, 0], ![-16, 0, 17]], ![![-1, 1, 0], ![-1, -7, 5], ![14, -20, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![21, 5, 1]] ![![17, 0, 0], ![-8, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-136, 17, 0]], ![![357, 85, 17], ![-238, -34, 17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-8, 1, 0]]], ![![![21, 5, 1]], ![![-14, -2, 1]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![8, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![8, 1, 0]] 
 ![![19, 0, 0], ![8, 1, 0], ![16, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![8, 1, 0], ![0, 9, 5], ![-70, -20, 8]]]
  hmulB := by decide  
  f := ![![![17, 2, 0], ![-38, 0, 0]], ![![8, 1, 0], ![-18, 0, 0]], ![![16, 0, -1], ![-36, 4, 0]]]
  g := ![![![1, 0, 0], ![-8, 19, 0], ![-16, 0, 19]], ![![0, 1, 0], ![-8, 9, 5], ![-2, -20, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-5, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-5, 1, 0]] 
 ![![19, 0, 0], ![14, 1, 0], ![15, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-5, 1, 0], ![0, -4, 5], ![-70, -20, -5]]]
  hmulB := by decide  
  f := ![![![31, -6, 0], ![114, 0, 0]], ![![26, -5, 0], ![96, 0, 0]], ![![25, -4, -1], ![92, 4, 0]]]
  g := ![![![1, 0, 0], ![-14, 19, 0], ![-15, 0, 19]], ![![-1, 1, 0], ![-1, -4, 5], ![15, -20, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-4, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-4, 1, 0]] 
 ![![19, 0, 0], ![15, 1, 0], ![9, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-4, 1, 0], ![0, -3, 5], ![-70, -20, -4]]]
  hmulB := by decide  
  f := ![![![37, -9, 0], ![171, 0, 0]], ![![33, -8, 0], ![153, 0, 0]], ![![23, -5, -1], ![107, 4, 0]]]
  g := ![![![1, 0, 0], ![-15, 19, 0], ![-9, 0, 19]], ![![-1, 1, 0], ![0, -3, 5], ![14, -20, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![8, 1, 0]] ![![19, 0, 0], ![-5, 1, 0]]
  ![![19, 0, 0], ![11, -3, 1]] where
 M := ![![![361, 0, 0], ![-95, 19, 0]], ![![152, 19, 0], ![-40, 4, 5]]]
 hmul := by decide  
 g := ![![![![8, 3, -1], ![19, 0, 0]], ![![-5, 1, 0], ![0, 0, 0]]], ![![![-3, 4, -1], ![19, 0, 0]], ![![-5, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![11, -3, 1]] ![![19, 0, 0], ![-4, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-76, 19, 0]], ![![209, -57, 19], ![-114, 0, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-4, 1, 0]]], ![![![11, -3, 1]], ![![-6, 0, -1]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![12, -5, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![12, -5, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![12, 18, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![12, -5, 1], ![-70, -13, -25], ![364, 86, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -18, 23]], ![![0, -1, 1], ![10, 19, -25], ![20, 10, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [21, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[13, 18], [21, 1], [16, 9], [1]], ![[21, 5], [1, 22], [20, 14], [1]]]
 h' := ![![[3, 22], [19, 8], [9, 1], [2, 3], [0, 1]], ![[0, 1], [20, 15], [12, 22], [11, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [11, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [21, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1344, -2614, -2642]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1320, 1954, -2642]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![2, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![2, 1, 0]] 
 ![![23, 0, 0], ![2, 1, 0], ![8, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![2, 1, 0], ![0, 3, 5], ![-70, -20, 2]]]
  hmulB := by decide  
  f := ![![![21, 10, 0], ![-230, 0, 0]], ![![-2, -1, 0], ![24, 0, 0]], ![![4, 0, -3], ![-42, 14, 0]]]
  g := ![![![1, 0, 0], ![-2, 23, 0], ![-8, 0, 23]], ![![0, 1, 0], ![-2, 3, 5], ![-2, -20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![12, -5, 1]] ![![23, 0, 0], ![2, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![46, 23, 0]], ![![276, -115, 23], ![-46, -23, -23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![2, 1, 0]]], ![![![12, -5, 1]], ![![-2, -1, -1]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [4, 25, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 24, 2], [4, 4, 27], [0, 1]]
 g := ![![[13, 2, 20], [21, 4], [0, 7, 13], [1]], ![[24, 19, 5, 12], [7, 24], [15, 15, 4, 26], [14, 19, 20, 8]], ![[7, 17, 5, 14], [15, 22], [19, 8], [10, 6, 26, 21]]]
 h' := ![![[6, 24, 2], [3, 10, 22], [0, 17, 2], [25, 4, 10], [0, 1]], ![[4, 4, 27], [23, 9, 21], [14, 10, 13], [15, 20, 19], [6, 24, 2]], ![[0, 1], [23, 10, 15], [24, 2, 14], [24, 5], [4, 4, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [12, 12, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [4, 25, 19, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1214230, -627328, -287651]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41870, -21632, -9919]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![618265, 107904, -111162]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![618265, 107904, -111162]] 
 ![![31, 0, 0], ![0, 31, 0], ![8, 6, 1]] where
  M :=![![![618265, 107904, -111162], ![7781340, 2949409, 539520], ![-9109548, -601812, 2841505]]]
  hmulB := by decide  
  f := ![![![280820968735, -7732617096, 12454147398]], ![![-871790317860, 24005403679, -38663085480]], ![![-73178480548, 2015024634, -3245397191]]]
  g := ![![![48631, 24996, -111162], ![111780, -9281, 539520], ![-1027148, -569382, 2841505]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 30], [0, 1]]
 g := ![![[27, 7], [16, 7], [26, 20], [6, 1]], ![[7, 24], [27, 24], [22, 11], [12, 30]]]
 h' := ![![[6, 30], [7, 10], [23, 21], [22, 19], [0, 1]], ![[0, 1], [5, 21], [25, 10], [12, 12], [6, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [25, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [17, 25, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134903, -155714, -127033]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28431, 19564, -127033]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![280820968735, -7732617096, 12454147398]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![280820968735, -7732617096, 12454147398]] 
 ![![31, 0, 0], ![1, 1, 0], ![12, 0, 1]] where
  M :=![![![280820968735, -7732617096, 12454147398], ![-871790317860, 24005403679, -38663085480], ![715641260292, -19705721652, 31738020775]]]
  hmulB := by decide  
  f := ![![![618265, 107904, -111162]], ![![270955, 98623, 13818]], ![![-54528, 22356, 48631]]]
  g := ![![![4487219905, -7732617096, 12454147398], ![-13930280509, 24005403679, -38663085480], ![11435184924, -19705721652, 31738020775]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![618265, 107904, -111162]] ![![280820968735, -7732617096, 12454147398]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB160I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB160I0 : PrimesBelowBoundCertificateInterval O 1 31 160 where
  m := 11
  g := ![3, 2, 3, 3, 1, 3, 2, 3, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB160I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N0, I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![9, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N0
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I5N2, I7N0, I7N1, I13N0, I17N1, I19N0, I19N1, I19N2, I23N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1, I5N2], [I7N0, I7N1, I7N1], [], [I13N0, I13N0, I13N0], [I17N1], [I19N0, I19N1, I19N2], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
