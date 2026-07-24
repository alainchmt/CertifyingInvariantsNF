
import IdealArithmetic.Examples.NF3_3_701244_1.RI3_3_701244_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![486, 13, -9]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![486, 13, -9]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![486, 13, -9], ![-1530, -27, 26], ![2210, -24, -27]]]
  hmulB := by decide  
  f := ![![![-1353, -567, -95]], ![![-8075, -3384, -567]], ![![-48195, -20197, -3384]]]
  g := ![![![243, 13, -9], ![-765, -27, 26], ![1105, -24, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![838007443, 26788328, -16251269]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![838007443, 26788328, -16251269]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![838007443, 26788328, -16251269], ![-2762715730, -88314890, 53576656], ![4554015760, 145576831, -88314890]]]
  hmulB := by decide  
  f := ![![![-345036, -144619, -24242]], ![![-2060570, -863415, -144619]], ![![-12465133, -5224236, -875536]]]
  g := ![![![427129356, 26788328, -16251269], ![-1408146193, -88314890, 53576656], ![2321165325, 145576831, -88314890]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![486, 13, -9]] ![![838007443, 26788328, -16251269]]
  ![![330370170968, 10560842359, -6406786196]] where
 M := ![![![330370170968, 10560842359, -6406786196]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![330370170968, 10560842359, -6406786196]] ![![838007443, 26788328, -16251269]]
  ![![2, 0, 0]] where
 M := ![![![218499451601572458794, 6984705238756211118, -4237305281685328448]]]
 hmul := by decide  
 g := ![![![![109249725800786229397, 3492352619378105559, -2118652640842664224]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 12, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![29, 12, 2]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![29, 12, 2], ![340, 143, 24], ![2040, 854, 143]]]
  hmulB := by decide  
  f := ![![![47, 8, -2]], ![![-82, -17, 4]], ![![469, 98, -23]]]
  g := ![![![1, 12, 2], ![10, 143, 24], ![63, 854, 143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![29, 12, 2]] ![![29, 12, 2]]
  ![![9001, 3772, 632]] where
 M := ![![![9001, 3772, 632]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![9001, 3772, 632]] ![![29, 12, 2]]
  ![![3, 0, 0]] where
 M := ![![![2832789, 1187136, 198906]]]
 hmul := by decide  
 g := ![![![![944263, 395712, 66302]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30525, 976, -592]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![30525, 976, -592]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![30525, 976, -592], ![-100640, -3219, 1952], ![165920, 5312, -3219]]]
  hmulB := by decide  
  f := ![![![-7063, -2960, -496]], ![![-16864, -7067, -1184]], ![![-100640, -42176, -7067]]]
  g := ![![![6105, 976, -592], ![-20128, -3219, 1952], ![33184, 5312, -3219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4482603, -143294, 86930]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-4482603, -143294, 86930]] 
 ![![5, 0, 0], ![2, 1, 0], ![3, 0, 1]] where
  M :=![![![-4482603, -143294, 86930], ![14778100, 472407, -286588], ![-24359980, -778708, 472407]]]
  hmulB := by decide  
  f := ![![![5345, 2218, 362]], ![![14446, 6083, 1032]], ![![78619, 32770, 5413]]]
  g := ![![![-891361, -143294, 86930], ![2938610, 472407, -286588], ![-4843957, -778708, 472407]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6409402523, 204887413, -124295942]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![6409402523, 204887413, -124295942]] 
 ![![5, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![6409402523, 204887413, -124295942], ![-21130310140, -675466171, 409774826], ![34830860210, 1113427471, -675466171]]]
  hmulB := by decide  
  f := ![![![-27243805, -11417059, -1912944]], ![![-81386379, -34106558, -5714590]], ![![-404526289, -169524756, -28404089]]]
  g := ![![![1233525622, 204887413, -124295942], ![-4066647221, -675466171, 409774826], ![6703395262, 1113427471, -675466171]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![30525, 976, -592]] ![![-4482603, -143294, 86930]]
  ![![-107986922815, -3451984982, 2094163418]] where
 M := ![![![-107986922815, -3451984982, 2094163418]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-107986922815, -3451984982, 2094163418]] ![![6409402523, 204887413, -124295942]]
  ![![5, 0, 0]] where
 M := ![![![-546248629003931146985, -17461763096890527795, 10593263204213321120]]]
 hmul := by decide  
 g := ![![![![-109249725800786229397, -3492352619378105559, 2118652640842664224]]]]
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
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38571, 1233, -748]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![38571, 1233, -748]] 
 ![![7, 0, 0], ![0, 7, 0], ![1, 1, 1]] where
  M :=![![![38571, 1233, -748], ![-127160, -4065, 2466], ![209610, 6701, -4065]]]
  hmulB := by decide  
  f := ![![![-63, -29, -6]], ![![-1020, -405, -58]], ![![-859, -371, -67]]]
  g := ![![![5617, 283, -748], ![-18518, -933, 2466], ![30525, 1538, -4065]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[1, 1], [2, 1]], ![[3, 6], [4, 6]]]
 h' := ![![[2, 6], [4, 6], [0, 1]], ![[0, 1], [2, 1], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2039, 75, 530]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-367, -65, 530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63, -29, -6]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-63, -29, -6]] 
 ![![7, 0, 0], ![5, 1, 0], ![5, 0, 1]] where
  M :=![![![-63, -29, -6], ![-1020, -405, -58], ![-4930, -2163, -405]]]
  hmulB := by decide  
  f := ![![![38571, 1233, -748]], ![![9385, 300, -182]], ![![57495, 1838, -1115]]]
  g := ![![![16, -29, -6], ![185, -405, -58], ![1130, -2163, -405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![38571, 1233, -748]] ![![-63, -29, -6]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [7, 0, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 9, 7], [2, 1, 4], [0, 1]]
 g := ![![[0, 7, 1], [4, 2, 1], []], ![[6, 9, 6, 6], [8, 8, 6, 7], [4, 5]], ![[9, 0, 6, 3], [10, 7, 4, 5], [7, 5]]]
 h' := ![![[0, 9, 7], [5, 8, 1], [0, 0, 1], [0, 1]], ![[2, 1, 4], [10, 4, 2], [5, 9, 1], [0, 9, 7]], ![[0, 1], [9, 10, 8], [10, 2, 9], [2, 1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8], []]
 b := ![[], [0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [7, 0, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-148093, 16104, -25014]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13463, 1464, -2274]
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

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-281907, -118069, -19752]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-281907, -118069, -19752]] 
 ![![13, 0, 0], ![0, 13, 0], ![3, 11, 1]] where
  M :=![![![-281907, -118069, -19752], ![-3357840, -1407771, -236138], ![-20071730, -8408853, -1407771]]]
  hmulB := by decide  
  f := ![![![294657021, 9419211, -5714210]], ![![-971415700, -31052949, 18838422]], ![![-630795059, -20164433, 12232851]]]
  g := ![![![-17127, 7631, -19752], ![-203802, 91519, -236138], ![-1219109, 544356, -1407771]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 0, 1] where
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
 h' := ![![[0, 12], [8], [0, 2], [0, 1]], ![[0, 1], [8], [0, 11], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [0, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [11, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1008, 425, 509]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-195, -398, 509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![294657021, 9419211, -5714210]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![294657021, 9419211, -5714210]] 
 ![![13, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![294657021, 9419211, -5714210], ![-971415700, -31052949, 18838422], ![1601265870, 51187177, -31052949]]]
  hmulB := by decide  
  f := ![![![-281907, -118069, -19752]], ![![-345036, -144619, -24242]], ![![-1652405, -692246, -115887]]]
  g := ![![![21965479, 9419211, -5714210], ![-72415078, -31052949, 18838422], ![119367839, 51187177, -31052949]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-281907, -118069, -19752]] ![![294657021, 9419211, -5714210]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57341, 1833, -1112]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![57341, 1833, -1112]] 
 ![![17, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![57341, 1833, -1112], ![-189040, -6043, 3666], ![311610, 9961, -6043]]]
  hmulB := by decide  
  f := ![![![-823, -187, 38]], ![![380, 79, -22]], ![![-1870, -437, 79]]]
  g := ![![![3373, 1833, -1112], ![-11120, -6043, 3666], ![18330, 9961, -6043]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 187, -38]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![823, 187, -38]] 
 ![![17, 0, 0], ![0, 17, 0], ![11, 0, 1]] where
  M :=![![![823, 187, -38], ![-6460, -1343, 374], ![31790, 7429, -1343]]]
  hmulB := by decide  
  f := ![![![-57341, -1833, 1112]], ![![189040, 6043, -3666]], ![![-55433, -1772, 1075]]]
  g := ![![![73, 11, -38], ![-622, -79, 374], ![2739, 437, -1343]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [7, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[9, 15], [16], [8], [1]], ![[16, 2], [16], [8], [1]]]
 h' := ![![[5, 16], [5, 7], [10, 4], [10, 5], [0, 1]], ![[0, 1], [6, 10], [13, 13], [1, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [4, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [7, 12, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![347, 187, 47]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, 11, 47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![57341, 1833, -1112]] ![![823, 187, -38]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [8, 3, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 11], [13, 7], [0, 1]]
 g := ![![[6, 8, 7], [4, 18, 17], [3, 1], []], ![[18, 11, 11], [4, 11, 5], [12, 11], []], ![[1, 0, 1], [14, 9, 16], [16, 7], []]]
 h' := ![![[9, 11], [6, 2, 11], [14, 2, 6], [0, 0, 1], [0, 1]], ![[13, 7], [3, 15, 1], [5, 13, 4], [5, 8, 7], [9, 11]], ![[0, 1], [10, 2, 7], [9, 4, 9], [17, 11, 11], [13, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17], []]
 b := ![[], [4, 11, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [8, 3, 16, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3021608, 1204410, 151240]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![159032, 63390, 7960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27840507, 889969, -539904]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![27840507, 889969, -539904]] 
 ![![23, 0, 0], ![0, 23, 0], ![2, 8, 1]] where
  M :=![![![27840507, 889969, -539904], ![-91783680, -2934021, 1779938], ![151294730, 4836393, -2934021]]]
  hmulB := by decide  
  f := ![![![-19791, -8301, -1394]], ![![-236980, -99249, -16602]], ![![-145504, -60967, -10211]]]
  g := ![![![1257405, 226487, -539904], ![-4145372, -746675, 1779938], ![6833164, 1230807, -2934021]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [10, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 22], [0, 1]]
 g := ![![[22, 4], [20, 3], [18, 8], [1]], ![[16, 19], [4, 20], [6, 15], [1]]]
 h' := ![![[10, 22], [7, 2], [4, 16], [13, 10], [0, 1]], ![[0, 1], [4, 21], [3, 7], [21, 13], [10, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [10, 13, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1022, -224, 64]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, -32, 64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19791, 8301, 1394]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![19791, 8301, 1394]] 
 ![![23, 0, 0], ![7, 1, 0], ![10, 0, 1]] where
  M :=![![![19791, 8301, 1394], ![236980, 99249, 16602], ![1411170, 591647, 99249]]]
  hmulB := by decide  
  f := ![![![-27840507, -889969, 539904]], ![![-4482603, -143294, 86930]], ![![-18682600, -597221, 362307]]]
  g := ![![![-2272, 8301, 1394], ![-27121, 99249, 16602], ![-161863, 591647, 99249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![27840507, 889969, -539904]] ![![19791, 8301, 1394]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [18, 1, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 25, 25], [13, 3, 4], [0, 1]]
 g := ![![[9, 8, 23], [28, 24], [5, 2, 16], [1]], ![[22, 3, 25, 5], [18, 5], [26, 21, 18, 5], [16, 18, 6, 23]], ![[11, 12, 23, 25], [21, 25], [13, 26, 16, 25], [12, 14, 4, 6]]]
 h' := ![![[12, 25, 25], [27, 17, 20], [26, 22, 16], [11, 28, 25], [0, 1]], ![[13, 3, 4], [15, 26, 21], [7, 22, 18], [19, 20, 21], [12, 25, 25]], ![[0, 1], [19, 15, 17], [7, 14, 24], [9, 10, 12], [13, 3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 9], []]
 b := ![[], [3, 20, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [18, 1, 4, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![234958, 119915, 29638]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8102, 4135, 1022]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31881, 7000, -1620]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31881, 7000, -1620]] 
 ![![31, 0, 0], ![0, 31, 0], ![10, 24, 1]] where
  M :=![![![31881, 7000, -1620], ![-275400, -60459, 14000], ![1190000, 261300, -60459]]]
  hmulB := by decide  
  f := ![![![-93849, -3000, 1820]], ![![309400, 9891, -6000]], ![![192810, 6164, -3739]]]
  g := ![![![1551, 1480, -1620], ![-13400, -12789, 14000], ![57890, 55236, -60459]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [8, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 30], [0, 1]]
 g := ![![[13, 4], [5, 25], [19, 28], [20, 1]], ![[0, 27], [9, 6], [21, 3], [9, 30]]]
 h' := ![![[20, 30], [22, 2], [3, 26], [26, 20], [0, 1]], ![[0, 1], [0, 29], [27, 5], [23, 11], [20, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [26, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [8, 11, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6766, -2090, 458]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-366, -422, 458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93849, 3000, -1820]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![93849, 3000, -1820]] 
 ![![31, 0, 0], ![14, 1, 0], ![26, 0, 1]] where
  M :=![![![93849, 3000, -1820], ![-309400, -9891, 6000], ![510000, 16300, -9891]]]
  hmulB := by decide  
  f := ![![![-31881, -7000, 1620]], ![![-5514, -1211, 280]], ![![-65126, -14300, 3309]]]
  g := ![![![3199, 3000, -1820], ![-10546, -9891, 6000], ![17386, 16300, -9891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31881, 7000, -1620]] ![![93849, 3000, -1820]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB187I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB187I0 : PrimesBelowBoundCertificateInterval O 1 31 187 where
  m := 11
  g := ![3, 3, 3, 2, 1, 2, 2, 1, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB187I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
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
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![17, 289]
    · exact ![6859]
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
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
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
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I5N2, I7N0, I7N1, I13N0, I13N1, I17N0, I23N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1, I5N2], [I7N0, I7N1], [], [I13N0, I13N1], [I17N0], [], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
