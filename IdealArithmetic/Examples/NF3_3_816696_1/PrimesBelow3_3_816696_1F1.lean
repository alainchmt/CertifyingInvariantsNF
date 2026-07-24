
import IdealArithmetic.Examples.NF3_3_816696_1.RI3_3_816696_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27246, -578, 643]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-27246, -578, 643]] 
 ![![37, 0, 0], ![0, 37, 0], ![36, 1, 1]] where
  M :=![![![-27246, -578, 643], ![46231, 981, -1091], ![-19819, -420, 468]]]
  hmulB := by decide  
  f := ![![![-24, -12, 5]], ![![367, 203, -31]], ![![-32, -15, 9]]]
  g := ![![![-1362, -33, 643], ![2311, 56, -1091], ![-991, -24, 468]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [10, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 36], [0, 1]]
 g := ![![[9, 26], [27], [8, 4], [34], [1]], ![[0, 11], [27], [18, 33], [34], [1]]]
 h' := ![![[21, 36], [25, 27], [31, 8], [19, 35], [27, 21], [0, 1]], ![[0, 1], [0, 10], [14, 29], [14, 2], [24, 16], [21, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [15, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [10, 16, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![324, 342, 342]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-324, 0, 342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 12, -5]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![24, 12, -5]] 
 ![![37, 0, 0], ![33, 1, 0], ![30, 0, 1]] where
  M :=![![![24, 12, -5], ![-367, -203, 31], ![687, 326, -184]]]
  hmulB := by decide  
  f := ![![![27246, 578, -643]], ![![23051, 489, -544]], ![![22627, 480, -534]]]
  g := ![![![-6, 12, -5], ![146, -203, 31], ![-123, 326, -184]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-27246, -578, 643]] ![![24, 12, -5]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, -70, 18]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-111, -70, 18]] 
 ![![41, 0, 0], ![0, 41, 0], ![28, 28, 1]] where
  M :=![![![-111, -70, 18], ![1348, 733, -192], ![-4376, -2326, 611]]]
  hmulB := by decide  
  f := ![![![-31, -22, -6]], ![![-404, -267, -72]], ![![-340, -226, -61]]]
  g := ![![![-15, -14, 18], ![164, 149, -192], ![-524, -474, 611]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [13, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 40], [0, 1]]
 g := ![![[1, 32], [23], [1], [27, 5], [1]], ![[36, 9], [23], [1], [3, 36], [1]]]
 h' := ![![[28, 40], [31, 14], [24, 33], [18, 40], [28, 28], [0, 1]], ![[0, 1], [13, 27], [5, 8], [31, 1], [33, 13], [28, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [9, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [13, 13, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3610, -1068, 2867]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2046, -1984, 2867]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 22, 6]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![31, 22, 6]] 
 ![![41, 0, 0], ![38, 1, 0], ![23, 0, 1]] where
  M :=![![![31, 22, 6], ![404, 267, 72], ![1760, 1174, 317]]]
  hmulB := by decide  
  f := ![![![111, 70, -18]], ![![70, 47, -12]], ![![169, 96, -25]]]
  g := ![![![-23, 22, 6], ![-278, 267, 72], ![-1223, 1174, 317]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-111, -70, 18]] ![![31, 22, 6]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133212, 88786, 23973]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![133212, 88786, 23973]] 
 ![![43, 0, 0], ![1, 1, 0], ![14, 0, 1]] where
  M :=![![![133212, 88786, 23973], ![1613297, 1075265, 290331], ![7094915, 4728772, 1276810]]]
  hmulB := by decide  
  f := ![![![1118, -1504, 321]], ![![591, 347, -90]], ![![-1873, -1710, 424]]]
  g := ![![![-6772, 88786, 23973], ![-82014, 1075265, 290331], ![-360679, 4728772, 1276810]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6472, 3428, -901]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![6472, 3428, -901]] 
 ![![43, 0, 0], ![6, 1, 0], ![4, 0, 1]] where
  M :=![![![6472, 3428, -901], ![-67399, -35699, 9383], ![213655, 113166, -29744]]]
  hmulB := by decide  
  f := ![![![5522, 134, -125]], ![![561, 19, -11]], ![![639, 36, -8]]]
  g := ![![![-244, 3428, -901], ![2541, -35699, 9383], ![-8055, 113166, -29744]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -22, -6]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-33, -22, -6]] 
 ![![43, 0, 0], ![36, 1, 0], ![24, 0, 1]] where
  M :=![![![-33, -22, -6], ![-404, -269, -72], ![-1760, -1174, -319]]]
  hmulB := by decide  
  f := ![![![-1283, -26, 30]], ![![-1024, -21, 24]], ![![-736, -14, 17]]]
  g := ![![![21, -22, -6], ![256, -269, -72], ![1120, -1174, -319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![133212, 88786, 23973]] ![![6472, 3428, -901]]
  ![![11765, 7840, 2114]] where
 M := ![![![11765, 7840, 2114]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![11765, 7840, 2114]] ![![-33, -22, -6]]
  ![![43, 0, 0]] where
 M := ![![![-7276245, -4849626, -1309436]]]
 hmul := by decide  
 g := ![![![![-169215, -112782, -30452]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [20, 11, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 42, 19], [25, 4, 28], [0, 1]]
 g := ![![[27, 7, 1], [26, 17, 36], [5, 13, 34], [40, 2, 1], []], ![[13, 17, 22, 44], [0, 5, 40, 33], [37, 8, 4, 35], [22, 10, 31, 22], [15, 32]], ![[44, 27, 0, 1], [36, 16, 0, 36], [16, 18], [25, 21, 18, 42], [6, 32]]]
 h' := ![![[24, 42, 19], [44, 21, 46], [41, 15, 6], [46, 37, 38], [0, 0, 1], [0, 1]], ![[25, 4, 28], [37, 0, 19], [36, 0, 27], [1, 8, 9], [41, 36, 4], [24, 42, 19]], ![[0, 1], [17, 26, 29], [15, 32, 14], [45, 2], [35, 11, 42], [25, 4, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 4], []]
 b := ![[], [4, 16, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [20, 11, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1158871809, -935919272, -590018777]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24656847, -19913176, -12553591]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7046, 3732, -981]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![7046, 3732, -981]] 
 ![![53, 0, 0], ![0, 53, 0], ![6, 9, 1]] where
  M :=![![![7046, 3732, -981], ![-73383, -38869, 10215], ![232599, 123198, -32386]]]
  hmulB := by decide  
  f := ![![![-6488, -138, 153]], ![![11001, 229, -261]], ![![1044, 21, -25]]]
  g := ![![![244, 237, -981], ![-2541, -2468, 10215], ![8055, 7824, -32386]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [1, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 52], [0, 1]]
 g := ![![[12, 1], [37], [5, 15], [44], [41, 1]], ![[0, 52], [37], [37, 38], [44], [29, 52]]]
 h' := ![![[41, 52], [41, 52], [48, 14], [47, 42], [12, 37], [0, 1]], ![[0, 1], [0, 1], [39, 39], [20, 11], [45, 16], [41, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [9, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [1, 12, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2402, -264, 2656]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-346, -456, 2656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6488, 138, -153]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![6488, 138, -153]] 
 ![![53, 0, 0], ![25, 1, 0], ![47, 0, 1]] where
  M :=![![![6488, 138, -153], ![-11001, -229, 261], ![4749, 120, -106]]]
  hmulB := by decide  
  f := ![![![-7046, -3732, 981]], ![![-1939, -1027, 270]], ![![-10637, -5634, 1481]]]
  g := ![![![193, 138, -153], ![-331, -229, 261], ![127, 120, -106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![7046, 3732, -981]] ![![6488, 138, -153]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71331, 37780, -9930]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![71331, 37780, -9930]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 12, 1]] where
  M :=![![![71331, 37780, -9930], ![-742810, -393439, 103410], ![2354690, 1247200, -327809]]]
  hmulB := by decide  
  f := ![![![-1811, -1220, -330]], ![![-22210, -14781, -3990]], ![![-6170, -4108, -1109]]]
  g := ![![![1209, 2660, -9930], ![-12590, -27701, 103410], ![39910, 87812, -327809]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [24, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 58], [0, 1]]
 g := ![![[21, 17], [48, 7], [3], [1, 9], [27, 1]], ![[8, 42], [1, 52], [3], [8, 50], [54, 58]]]
 h' := ![![[27, 58], [28, 28], [32, 19], [35, 48], [1, 56], [0, 1]], ![[0, 1], [17, 31], [14, 40], [33, 11], [38, 3], [27, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [2, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [24, 32, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![354, 342, 294]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, -54, 294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1811, 1220, 330]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1811, 1220, 330]] 
 ![![59, 0, 0], ![22, 1, 0], ![3, 0, 1]] where
  M :=![![![1811, 1220, 330], ![22210, 14781, 3990], ![97510, 65000, 17551]]]
  hmulB := by decide  
  f := ![![![-71331, -37780, 9930]], ![![-14008, -7419, 1950]], ![![-43537, -23060, 6061]]]
  g := ![![![-441, 1220, 330], ![-5338, 14781, 3990], ![-23477, 65000, 17551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![71331, 37780, -9930]] ![![1811, 1220, 330]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5083988, -3388486, -914921]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-5083988, -3388486, -914921]] 
 ![![61, 0, 0], ![0, 61, 0], ![54, 51, 1]] where
  M :=![![![-5083988, -3388486, -914921], ![-61570905, -41037105, -11080379], ![-270774899, -180471896, -48728998]]]
  hmulB := by decide  
  f := ![![![15446, 708, -451]], ![![-32729, -4655, 1673]], ![![-13110, -3047, 939]]]
  g := ![![![726586, 709385, -914921], ![8799501, 8591184, -11080379], ![38698213, 37782082, -48728998]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [30, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 60], [0, 1]]
 g := ![![[56, 41], [41], [26, 48], [16, 57], [28, 1]], ![[45, 20], [41], [28, 13], [26, 4], [56, 60]]]
 h' := ![![[28, 60], [37, 38], [13, 23], [8, 32], [14, 22], [0, 1]], ![[0, 1], [3, 23], [47, 38], [50, 29], [20, 39], [28, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [57, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [30, 33, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10426, 7034, 1944]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1550, -1510, 1944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15446, -708, 451]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-15446, -708, 451]] 
 ![![61, 0, 0], ![29, 1, 0], ![34, 0, 1]] where
  M :=![![![-15446, -708, 451], ![32729, 4655, -1673], ![-35385, -13306, 3690]]]
  hmulB := by decide  
  f := ![![![5083988, 3388486, 914921]], ![![3426337, 2283659, 616608]], ![![7272631, 4847220, 1308792]]]
  g := ![![![-168, -708, 451], ![-744, 4655, -1673], ![3689, -13306, 3690]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-5083988, -3388486, -914921]] ![![-15446, -708, 451]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [34, 24, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 25, 65], [54, 41, 2], [0, 1]]
 g := ![![[61, 23, 65], [21, 12, 6], [6, 54], [17, 14], [57, 1], []], ![[47, 23, 56, 56], [7, 17, 39, 25], [27, 22], [22, 40], [32, 6], [61, 4]], ![[27, 24, 63, 2], [42, 14, 58, 13], [26, 62], [20, 17], [54, 22], [57, 4]]]
 h' := ![![[3, 25, 65], [23, 15, 47], [18, 45, 41], [50, 37, 11], [5, 5, 9], [0, 0, 1], [0, 1]], ![[54, 41, 2], [29, 29, 21], [42, 32, 50], [25, 50, 42], [61, 6, 24], [12, 24, 41], [3, 25, 65]], ![[0, 1], [33, 23, 66], [1, 57, 43], [9, 47, 14], [32, 56, 34], [40, 43, 25], [54, 41, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 26], []]
 b := ![[], [30, 63, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [34, 24, 10, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![312421, 135340, -113900]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4663, 2020, -1700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [10, 44, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 37, 52], [9, 33, 19], [0, 1]]
 g := ![![[70, 59, 32], [66, 34, 43], [63, 20, 1], [0, 24], [19, 1], []], ![[16, 63, 35, 21], [50, 57, 27, 17], [30, 51, 21, 33], [62, 6], [11, 24], [57, 6]], ![[58, 50, 39, 60], [4, 56, 31, 64], [41, 59, 45, 27], [44, 54], [42, 20], [19, 6]]]
 h' := ![![[10, 37, 52], [50, 32, 48], [9, 40, 55], [32, 36, 1], [23, 6, 33], [0, 0, 1], [0, 1]], ![[9, 33, 19], [33, 60, 53], [48, 56, 61], [64, 1, 59], [51, 35, 52], [27, 18, 33], [10, 37, 52]], ![[0, 1], [5, 50, 41], [54, 46, 26], [34, 34, 11], [30, 30, 57], [33, 53, 37], [9, 33, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 46], []]
 b := ![[], [61, 62, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [10, 44, 52, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![578934, 550747, 490326]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8154, 7757, 6906]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10219, -3510, 990]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-10219, -3510, 990]] 
 ![![73, 0, 0], ![0, 73, 0], ![57, 23, 1]] where
  M :=![![![-10219, -3510, 990], ![73800, 35861, -9540], ![-216540, -113310, 29831]]]
  hmulB := by decide  
  f := ![![![153533, 102330, 27630]], ![![1859400, 1239293, 334620]], ![![817737, 545023, 147161]]]
  g := ![![![-913, -360, 990], ![8460, 3497, -9540], ![-26259, -10951, 29831]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [63, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 72], [0, 1]]
 g := ![![[55, 72], [12], [8], [54, 35], [61], [1]], ![[16, 1], [12], [8], [32, 38], [61], [1]]]
 h' := ![![[39, 72], [28, 46], [45, 31], [29, 9], [53, 20], [10, 39], [0, 1]], ![[0, 1], [70, 27], [13, 42], [15, 64], [30, 53], [71, 34], [39, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [4, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [63, 34, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![888, 950, 930]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-714, -280, 930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153533, 102330, 27630]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![153533, 102330, 27630]] 
 ![![73, 0, 0], ![3, 1, 0], ![22, 0, 1]] where
  M :=![![![153533, 102330, 27630], ![1859400, 1239293, 334620], ![8177220, 5450130, 1471583]]]
  hmulB := by decide  
  f := ![![![-10219, -3510, 990]], ![![591, 347, -90]], ![![-6046, -2610, 707]]]
  g := ![![![-10429, 102330, 27630], ![-126303, 1239293, 334620], ![-555452, 5450130, 1471583]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-10219, -3510, 990]] ![![153533, 102330, 27630]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [38, 45, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 31, 40], [25, 47, 39], [0, 1]]
 g := ![![[22, 45, 44], [40, 17, 64], [66, 60, 8], [23, 55, 1], [58, 1], []], ![[24, 63, 78, 11], [32, 33, 54, 22], [7, 51, 62, 31], [18, 52, 25, 45], [56, 76], [6, 20]], ![[18, 48, 20, 7], [17, 66, 61, 54], [10, 59, 12, 6], [55, 49, 67, 7], [14, 13], [7, 20]]]
 h' := ![![[33, 31, 40], [60, 8, 26], [20, 68, 71], [74, 20, 61], [8, 38, 1], [0, 0, 1], [0, 1]], ![[25, 47, 39], [37, 41, 41], [37, 63, 53], [9, 28, 33], [69, 61, 66], [71, 68, 47], [33, 31, 40]], ![[0, 1], [35, 30, 12], [33, 27, 34], [37, 31, 64], [53, 59, 12], [43, 11, 31], [25, 47, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 14], []]
 b := ![[], [77, 49, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [38, 45, 21, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5433304, -2721708, 1158456]
  a := ![-2, -12, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68776, -34452, 14664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB201I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB201I1 : PrimesBelowBoundCertificateInterval O 31 79 201 where
  m := 11
  g := ![2, 2, 3, 1, 2, 2, 2, 1, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB201I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N0, I43N1, I43N2, I53N1, I59N1, I61N1, I73N1]
  Il := ![[I37N1], [I41N1], [I43N0, I43N1, I43N2], [], [I53N1], [I59N1], [I61N1], [], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
