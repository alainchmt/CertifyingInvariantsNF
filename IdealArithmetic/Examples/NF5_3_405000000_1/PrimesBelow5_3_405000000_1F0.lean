
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2317, 5946, -1017, 228, -759]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-2317, 5946, -1017, 228, -759]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-2317, 5946, -1017, 228, -759], ![-456, 1175, -201, 45, -150], ![-90, 234, -40, 9, -30], ![-18, 48, -9, 2, -6], ![-582, 1491, -255, 57, -190]]]
  hmulB := by decide  
  f := ![![![4, 51, -108, -6, -39]], ![![6, 74, -159, -9, -57]], ![![18, 216, -466, -27, -168]], ![![54, 636, -1377, -76, -498]], ![![35, 429, -924, -51, -331]]]
  g := ![![![-779, 5946, -1017, 228, -759], ![-153, 1175, -201, 45, -150], ![-30, 234, -40, 9, -30], ![-6, 48, -9, 2, -6], ![-196, 1491, -255, 57, -190]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 74, -159, -9, -57]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![6, 74, -159, -9, -57]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![6, 74, -159, -9, -57], ![18, 216, -466, -27, -168], ![54, 636, -1377, -76, -498], ![152, 1894, -4074, -229, -1452], ![96, 1183, -2544, -151, -911]]]
  hmulB := by decide  
  f := ![![![-23582, 60405, -10330, 2317, -7710]], ![![-2317, 5946, -1017, 228, -759]], ![![-456, 1175, -201, 45, -150]], ![![-90, 234, -40, 9, -30]], ![![-2963, 7584, -1297, 291, -968]]]
  g := ![![![3, 74, -159, -9, -57], ![9, 216, -466, -27, -168], ![27, 636, -1377, -76, -498], ![76, 1894, -4074, -229, -1452], ![48, 1183, -2544, -151, -911]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -33, 6, 0, 2]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![13, -33, 6, 0, 2]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![13, -33, 6, 0, 2], ![0, 5, -15, 2, 4], ![-4, -12, 47, -27, 20], ![54, -138, 87, 61, -122], ![4, 58, -163, 68, -31]]]
  hmulB := by decide  
  f := ![![![156, -950, 113, -37, 106]], ![![115, -646, 3, -31, 48]], ![![103, -443, -197, -37, -32]], ![![115, -147, -732, -65, -228]], ![![107, -305, -433, -49, -119]]]
  g := ![![![19, -33, 6, 0, 2], ![2, 5, -15, 2, 4], ![-16, -12, 47, -27, 20], ![83, -138, 87, 61, -122], ![36, 58, -163, 68, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-2317, 5946, -1017, 228, -759]] ![![6, 74, -159, -9, -57]]
  ![![0, 1, 0, 0, 0]] where
 M := ![![![0, 1, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![0, 1, 0, 0, 0]] ![![6, 74, -159, -9, -57]]
  ![![18, 216, -466, -27, -168]] where
 M := ![![![18, 216, -466, -27, -168]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![18, 216, -466, -27, -168]] ![![13, -33, 6, 0, 2]]
  ![![-32, 60, 1, -57, 82]] where
 M := ![![![-32, 60, 1, -57, 82]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-32, 60, 1, -57, 82]] ![![13, -33, 6, 0, 2]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-3170, 13966, -19370, 2192, 4608]]]
 hmul := by decide  
 g := ![![![![-1585, 6983, -9685, 1096, 2304]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, -1013, 175, -38, 130]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![347, -1013, 175, -38, 130]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![347, -1013, 175, -38, 130], ![76, -249, 43, -9, 32], ![18, -70, 12, -3, 10], ![6, -28, 11, -2, 2], ![84, -230, 39, -7, 27]]]
  hmulB := by decide  
  f := ![![![235, 2827, -6103, -346, -2196]], ![![309, 3718, -8026, -455, -2888]], ![![836, 10060, -21716, -1231, -7814]], ![![2079, 25021, -54010, -3062, -19434]], ![![1337, 16089, -34730, -1969, -12497]]]
  g := ![![![306, -1013, 175, -38, 130], ![72, -249, 43, -9, 32], ![19, -70, 12, -3, 10], ![4, -28, 11, -2, 2], ![72, -230, 39, -7, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153, 392, -67, 15, -50]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-153, 392, -67, 15, -50]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-153, 392, -67, 15, -50], ![-30, 77, -13, 3, -10], ![-6, 16, -4, 1, -2], ![-2, 4, 1, -2, 2], ![-38, 96, -13, 3, -13]]]
  hmulB := by decide  
  f := ![![![-7, 52, -19, 1, -10]], ![![-3, 29, -18, 0, -8]], ![![-4, 52, -44, -1, -18]], ![![1, 60, -96, -5, -36]], ![![2, 28, -57, -3, -21]]]
  g := ![![![-142, 392, -67, 15, -50], ![-28, 77, -13, 3, -10], ![-5, 16, -4, 1, -2], ![-2, 4, 1, -2, 2], ![-37, 96, -13, 3, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55039, -140767, 24070, -5401, 17966]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![55039, -140767, 24070, -5401, 17966]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![55039, -140767, 24070, -5401, 17966], ![10802, -27627, 4724, -1060, 3526], ![2120, -5422, 927, -208, 692], ![416, -1064, 182, -41, 136], ![13838, -35392, 6052, -1358, 4517]]]
  hmulB := by decide  
  f := ![![![-25, 165, -36, 5, -24]], ![![-20, 137, -36, 4, -22]], ![![-18, 132, -49, 2, -24]], ![![-14, 138, -78, -3, -40]], ![![2, 22, -40, 0, -19]]]
  g := ![![![99745, -140767, 24070, -5401, 17966], ![19576, -27627, 4724, -1060, 3526], ![3842, -5422, 927, -208, 692], ![754, -1064, 182, -41, 136], ![25078, -35392, 6052, -1358, 4517]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![347, -1013, 175, -38, 130]] ![![347, -1013, 175, -38, 130]]
  ![![57263, -140360, 23918, -5428, 17878]] where
 M := ![![![57263, -140360, 23918, -5428, 17878]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![57263, -140360, 23918, -5428, 17878]] ![![347, -1013, 175, -38, 130]]
  ![![11102609, -28691995, 4910095, -1098798, 3663700]] where
 M := ![![![11102609, -28691995, 4910095, -1098798, 3663700]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![11102609, -28691995, 4910095, -1098798, 3663700]] ![![-153, 392, -67, 15, -50]]
  ![![-1004422901, 2568820641, -439246146, 98561941, -327856386]] where
 M := ![![![-1004422901, 2568820641, -439246146, 98561941, -327856386]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-1004422901, 2568820641, -439246146, 98561941, -327856386]] ![![55039, -140767, 24070, -5401, 17966]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-32961108215589, 84301006567860, -14414780271138, 3234489339816, -10759281463818]]]
 hmul := by decide  
 g := ![![![![-10987036071863, 28100335522620, -4804926757046, 1078163113272, -3586427154606]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, -1416, 254, -48, 186]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![197, -1416, 254, -48, 186]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![197, -1416, 254, -48, 186], ![96, -643, 114, -22, 84], ![44, -284, 47, -10, 36], ![20, -120, 10, -5, 12], ![20, -162, 22, -6, 19]]]
  hmulB := by decide  
  f := ![![![1, 4, -14, 8, -6]], ![![-3, 9, -8, -2, 6]], ![![8, -36, 51, -6, -12]], ![![25, 12, -144, 103, -90]], ![![-28, 118, -158, 14, 43]]]
  g := ![![![129, -1416, 254, -48, 186], ![61, -643, 114, -22, 84], ![30, -284, 47, -10, 36], ![21, -120, 10, -5, 12], ![20, -162, 22, -6, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![197, -1416, 254, -48, 186]] ![![197, -1416, 254, -48, 186]]
  ![![-83191, 535028, -95836, 18280, -70200]] where
 M := ![![![-83191, 535028, -95836, 18280, -70200]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-83191, 535028, -95836, 18280, -70200]] ![![197, -1416, 254, -48, 186]]
  ![![29718877, -189828324, 33996786, -6489288, 24904290]] where
 M := ![![![29718877, -189828324, 33996786, -6489288, 24904290]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![29718877, -189828324, 33996786, -6489288, 24904290]] ![![197, -1416, 254, -48, 186]]
  ![![-10504741711, 67066814856, -12010983736, 2292769872, -8798673744]] where
 M := ![![![-10504741711, 67066814856, -12010983736, 2292769872, -8798673744]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-10504741711, 67066814856, -12010983736, 2292769872, -8798673744]] ![![197, -1416, 254, -48, 186]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![3710378747285, -23687875546720, 4242253139750, -809804294240, 3107673512490]]]
 hmul := by decide  
 g := ![![![![742075749457, -4737575109344, 848450627950, -161960858848, 621534702498]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123, 852, -153, 29, -112]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-123, 852, -153, 29, -112]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![3, 5, 1, 1, 0], ![6, 4, 5, 0, 1]] where
  M :=![![![-123, 852, -153, 29, -112], ![-58, 383, -69, 13, -50], ![-26, 168, -28, 5, -22], ![-10, 72, -15, 6, -14], ![-14, 106, -25, 5, -13]]]
  hmulB := by decide  
  f := ![![![-1, -28, 55, 3, 20]], ![![-6, -75, 161, 9, 58]], ![![-18, -220, 474, 27, 170]], ![![-15, -189, 405, 23, 146]], ![![-22, -282, 603, 34, 217]]]
  g := ![![![66, 165, 54, 29, -112], ![29, 74, 24, 13, -50], ![13, 33, 11, 5, -22], ![8, 14, 7, 6, -14], ![7, 19, 5, 5, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [2, 6, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2], [2, 4], [0, 1]]
 g := ![![[2, 2, 4], [1]], ![[2, 3, 2], [1]], ![[1, 2, 1], [1]]]
 h' := ![![[3, 2], [5, 1, 5], [0, 1]], ![[2, 4], [4, 6, 6], [3, 2]], ![[0, 1], [6, 0, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [4, 5, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [2, 6, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1304193, 2547790, 28021, -2731629, 3276309]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1823880, 442957, -1945985, -2731629, 3276309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -145, 25, -4, 18]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![23, -145, 25, -4, 18]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![23, -145, 25, -4, 18], ![8, -57, 5, -3, 12], ![6, -46, 42, -13, 6], ![26, -44, -31, 56, -66], ![-8, 46, -103, 23, 11]]]
  hmulB := by decide  
  f := ![![![25555, -65357, 11171, -2508, 8340]], ![![8018, -20505, 3503, -787, 2616]], ![![11093, -28367, 4843, -1089, 3618]], ![![3679, -9399, 1590, -362, 1194]], ![![4569, -11679, 1986, -449, 1487]]]
  g := ![![![32, -145, 25, -4, 18], ![14, -57, 5, -3, 12], ![-3, -46, 42, -13, 6], ![31, -44, -31, 56, -66], ![25, 46, -103, 23, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197, 1254, -223, 43, -164]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-197, 1254, -223, 43, -164]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-197, 1254, -223, 43, -164], ![-86, 545, -93, 19, -70], ![-38, 232, -28, 9, -26], ![-18, 84, 25, 6, 2], ![-26, 146, -1, 7, -11]]]
  hmulB := by decide  
  f := ![![![-31, 78, -11, 1, -8]], ![![-18, 45, -5, 1, -6]], ![![-23, 62, -19, 4, -6]], ![![-11, 18, 12, -17, 18]], ![![-24, 50, 21, -5, -11]]]
  g := ![![![-451, 1254, -223, 43, -164], ![-200, 545, -93, 19, -70], ![-97, 232, -28, 9, -26], ![-71, 84, 25, 6, 2], ![-78, 146, -1, 7, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-123, 852, -153, 29, -112]] ![![23, -145, 25, -4, 18]]
  ![![4719, -30119, 5396, -1027, 3946]] where
 M := ![![![4719, -30119, 5396, -1027, 3946]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![4719, -30119, 5396, -1027, 3946]] ![![-197, 1254, -223, 43, -164]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![1371433, -8755509, 1568021, -299320, 1148658]]]
 hmul := by decide  
 g := ![![![![195919, -1250787, 224003, -42760, 164094]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 97, 50, -93, 106]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-47, 97, 50, -93, 106]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![9, 6, 4, 4, 1]] where
  M :=![![![-47, 97, 50, -93, 106], ![186, -657, 772, 24, -346], ![-48, 1618, -3699, 1416, -548], ![-2832, 4976, 934, -5435, 7400], ![814, -6116, 11132, -3058, -77]]]
  hmulB := by decide  
  f := ![![![-303, -615, 2388, 161, 824]], ![![-322, -3277, 7284, 418, 2614]], ![![-836, -9942, 21503, 1220, 7736]], ![![-2440, -29340, 63342, 3591, 22792]], ![![-1759, -18241, 40400, 2315, 14503]]]
  g := ![![![-91, -49, -34, -47, 106], ![300, 129, 196, 128, -346], ![444, 446, -137, 328, -548], ![-6312, -3584, -2606, -3185, 7400], ![137, -514, 1040, -250, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [2, 8, 9, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10, 7, 6], [9, 5, 5, 6], [6, 6, 10, 10], [0, 1]]
 g := ![![[2, 9, 1, 4], [0, 1], []], ![[10, 8, 7, 10, 1, 6], [6, 5, 5, 9, 9, 7], [10, 7, 3]], ![[4, 5, 9, 9, 9, 7], [8, 5, 6, 0, 3, 6], [3, 5, 3]], ![[1, 10, 4, 4, 9, 8], [4, 9, 7, 7, 7, 8], [2, 2, 1]]]
 h' := ![![[7, 10, 7, 6], [0, 9, 3, 2], [0, 0, 1], [0, 1]], ![[9, 5, 5, 6], [1, 1, 6, 10], [7, 2, 2, 5], [7, 10, 7, 6]], ![[6, 6, 10, 10], [9, 9, 1, 5], [9, 1, 9, 1], [9, 5, 5, 6]], ![[0, 1], [9, 3, 1, 5], [10, 8, 10, 5], [6, 6, 10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 1], []]
 b := ![[], [], [2, 4, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [2, 8, 9, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-884235874, 3828737334, -5238575574, 547192128, 1314390822]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1155795752, -368873418, -954194442, -428215560, 1314390822]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-303, -615, 2388, 161, 824]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-303, -615, 2388, 161, 824]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-303, -615, 2388, 161, 824], ![-322, -3277, 7284, 418, 2614], ![-836, -9942, 21503, 1220, 7736], ![-2440, -29340, 63342, 3591, 22792], ![-1586, -18326, 39824, 2264, 14321]]]
  hmulB := by decide  
  f := ![![![-47, 97, 50, -93, 106]], ![![-13, 2, 102, -57, 36]], ![![-30, 200, -309, 78, 8]], ![![-266, 470, 94, -511, 692]], ![![74, -556, 1012, -278, -7]]]
  g := ![![![-968, -615, 2388, 161, 824], ![-1993, -3277, 7284, 418, 2614], ![-5700, -9942, 21503, 1220, 7736], ![-16754, -29340, 63342, 3591, 22792], ![-10616, -18326, 39824, 2264, 14321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-47, 97, 50, -93, 106]] ![![-303, -615, 2388, 161, 824]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6963, 44566, -7985, 1523, -5848]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-6963, 44566, -7985, 1523, -5848]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![5, 2, 2, 1, 0], ![4, 12, 3, 0, 1]] where
  M :=![![![-6963, 44566, -7985, 1523, -5848], ![-3046, 19475, -3497, 665, -2558], ![-1330, 8516, -1552, 289, -1126], ![-578, 3752, -751, 122, -518], ![-874, 5646, -1061, 189, -757]]]
  hmulB := by decide  
  f := ![![![5, -22, 29, -5, -4]], ![![10, 11, -73, 47, -38]], ![![-94, 256, -190, -91, 206]], ![![3, -52, 112, -41, 14]], ![![8, 22, -91, 50, -35]]]
  g := ![![![678, 8592, 501, 1523, -5848], ![297, 3757, 219, 665, -2558], ![133, 1650, 96, 289, -1126], ![68, 748, 43, 122, -518], ![93, 1104, 64, 189, -757]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [7, 6, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12, 5], [12, 0, 8], [0, 1]]
 g := ![![[2, 12, 12], [3, 4], [1]], ![[9, 10, 2, 8], [0, 3], [7, 9, 0, 8]], ![[8, 5, 8, 7], [9, 10], [0, 6, 3, 5]]]
 h' := ![![[12, 12, 5], [2, 12, 8], [6, 7, 11], [0, 1]], ![[12, 0, 8], [4, 2, 8], [2, 9, 9], [12, 12, 5]], ![[0, 1], [3, 12, 10], [12, 10, 6], [12, 0, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 3], []]
 b := ![[], [10, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [7, 6, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3194, 16873, -24003, -40, 3236]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1226, -1683, -2587, -40, 3236]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -22, 29, -5, -4]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![5, -22, 29, -5, -4]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![7, 11, 1, 0, 0], ![1, 3, 0, 1, 0], ![6, 10, 0, 0, 1]] where
  M :=![![![5, -22, 29, -5, -4], ![10, 11, -73, 47, -38], ![-94, 256, -190, -91, 206], ![182, -1100, 1837, -420, -134], ![246, -526, 147, 379, -601]]]
  hmulB := by decide  
  f := ![![![-6963, 44566, -7985, 1523, -5848]], ![![-3046, 19475, -3497, 665, -2558]], ![![-6429, 41131, -7378, 1405, -5400]], ![![-1283, 8211, -1479, 280, -1080]], ![![-5624, 35984, -6457, 1229, -4725]]]
  g := ![![![-13, -22, 29, -5, -4], ![54, 81, -73, 47, -38], ![7, 43, -190, -91, 206], ![-881, -1439, 1837, -420, -134], ![188, 210, 147, 379, -601]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [10, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[10, 4], [10], [4, 1]], ![[0, 9], [10], [8, 12]]]
 h' := ![![[4, 12], [5, 2], [12, 6], [0, 1]], ![[0, 1], [0, 11], [10, 7], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [2, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [10, 9, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7780, -45486, 72398, -11248, -6166]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34674, -57420, 72398, -11248, -6166]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-6963, 44566, -7985, 1523, -5848]] ![![5, -22, 29, -5, -4]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17257, -44218, 7562, -1696, 5644]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17257, -44218, 7562, -1696, 5644]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![9, 4, 12, 1, 0], ![13, 15, 1, 0, 1]] where
  M :=![![![17257, -44218, 7562, -1696, 5644], ![3392, -8711, 1490, -334, 1112], ![668, -1724, 295, -66, 220], ![132, -344, 58, -13, 44], ![4336, -11100, 1898, -426, 1417]]]
  hmulB := by decide  
  f := ![![![1, 2, -10, 0, -4]], ![![0, 17, -34, -2, -8]], ![![4, 28, -61, -14, -28]], ![![5, 30, -72, -9, -32]], ![![1, 25, -55, -2, -15]]]
  g := ![![![-2403, -7182, 1310, -1696, 5644], ![-474, -1415, 258, -334, 1112], ![-94, -280, 51, -66, 220], ![-19, -56, 10, -13, 44], ![-603, -1803, 329, -426, 1417]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [7, 3, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 10, 14], [6, 6, 3], [0, 1]]
 g := ![![[10, 15, 15], [12, 16], [4, 1], []], ![[14, 4, 0, 7], [0, 1], [10, 2], [10, 9]], ![[4, 5, 9, 14], [15, 8], [0, 15], [4, 9]]]
 h' := ![![[15, 10, 14], [3, 15, 7], [6, 15, 13], [0, 0, 1], [0, 1]], ![[6, 6, 3], [4, 1, 14], [2, 2, 16], [2, 3, 6], [15, 10, 14]], ![[0, 1], [13, 1, 13], [13, 0, 5], [8, 14, 10], [6, 6, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 15], []]
 b := ![[], [8, 12, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [7, 3, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8132575, 38128550, -55281694, 7888960, 10815162]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12925313, -9156160, -9456728, 7888960, 10815162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, 10, 0, 4]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-1, -2, 10, 0, 4]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![9, 5, 1, 0, 0], ![6, 1, 0, 1, 0], ![7, 4, 0, 0, 1]] where
  M :=![![![-1, -2, 10, 0, 4], ![0, -17, 34, 2, 8], ![-4, -28, 61, 14, 28], ![-28, -88, 266, -23, 140], ![0, -116, 234, -10, 55]]]
  hmulB := by decide  
  f := ![![![-17257, 44218, -7562, 1696, -5644]], ![![-3392, 8711, -1490, 334, -1112]], ![![-10173, 26073, -4459, 1000, -3328]], ![![-6298, 16139, -2760, 619, -2060]], ![![-8159, 20910, -3576, 802, -2669]]]
  g := ![![![-7, -4, 10, 0, 4], ![-22, -13, 34, 2, 8], ![-49, -27, 61, 14, 28], ![-192, -115, 266, -23, 140], ![-143, -88, 234, -10, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [5, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16], [0, 1]]
 g := ![![[15, 13], [1], [15], [1]], ![[9, 4], [1], [15], [1]]]
 h' := ![![[10, 16], [13, 8], [1, 16], [12, 10], [0, 1]], ![[0, 1], [8, 9], [8, 1], [10, 7], [10, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [15, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [5, 7, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-605, -29357, 68320, -17401, 15702]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36529, -24492, 68320, -17401, 15702]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17257, -44218, 7562, -1696, 5644]] ![![-1, -2, 10, 0, 4]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 107, -154, 37, 6]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-21, 107, -154, 37, 6]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![10, 14, 1, 1, 0], ![14, 17, 3, 0, 1]] where
  M :=![![![-21, 107, -154, 37, 6], ![-74, 29, 272, -240, 234], ![480, -1490, 1415, 284, -972], ![-568, 4936, -9386, 2791, -240], ![-1342, 3412, -2120, -1534, 3041]]]
  hmulB := by decide  
  f := ![![![-181, -877, 2748, 175, 960]], ![![-350, -3671, 8288, 478, 2970]], ![![-956, -11274, 24493, 1392, 8808]], ![![-550, -5518, 12641, 733, 4524]], ![![-690, -6815, 15697, 912, 5615]]]
  g := ![![![-25, -27, -11, 37, 6], ![-50, -31, -10, -240, 234], ![592, 582, 213, 284, -972], ![-1322, -1582, -603, 2791, -240], ![-1504, -1411, -511, -1534, 3041]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [5, 14, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 5, 14], [11, 13, 5], [0, 1]]
 g := ![![[4, 14, 5], [5, 0, 5], [10, 1], []], ![[4, 6, 7, 10], [6, 18], [12, 17], [10, 6]], ![[16, 1, 0, 7], [17, 17, 18, 6], [17, 6], [0, 6]]]
 h' := ![![[18, 5, 14], [13, 17, 9], [7, 7, 10], [0, 0, 1], [0, 1]], ![[11, 13, 5], [11, 4, 13], [4, 2], [8, 10, 13], [18, 5, 14]], ![[0, 1], [16, 17, 16], [2, 10, 9], [7, 9, 5], [11, 13, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 3], []]
 b := ![[], [6, 13, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [5, 14, 9, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20853, 234450, -474280, 155598, -32094]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-59343, -73596, -28084, 155598, -32094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181, -877, 2748, 175, 960]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-181, -877, 2748, 175, 960]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![11, 18, 1, 0, 0], ![11, 10, 0, 1, 0], ![8, 14, 0, 0, 1]] where
  M :=![![![-181, -877, 2748, 175, 960], ![-350, -3671, 8288, 478, 2970], ![-956, -11274, 24493, 1392, 8808], ![-2784, -33404, 72174, 4093, 25968], ![-1758, -20978, 45396, 2576, 16331]]]
  hmulB := by decide  
  f := ![![![-21, 107, -154, 37, 6]], ![![-74, 29, 272, -240, 234]], ![![-57, 11, 243, -191, 174]], ![![-81, 337, -440, 42, 114]], ![![-134, 246, 24, -242, 335]]]
  g := ![![![-2106, -3449, 2748, 175, 960], ![-6344, -10485, 8288, 478, 2970], ![-18745, -31020, 24493, 1392, 8808], ![-55235, -91422, 72174, 4093, 25968], ![-34742, -57500, 45396, 2576, 16331]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 18], [0, 1]]
 g := ![![[0, 1], [], [], [1]], ![[0, 18], [], [], [1]]]
 h' := ![![[0, 18], [0, 1], [1], [18], [0, 1]], ![[0, 1], [0, 18], [1], [18], [0, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10771, -54821, 80834, -8406, -12165]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36243, -66077, 80834, -8406, -12165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-21, 107, -154, 37, 6]] ![![-181, -877, 2748, 175, 960]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [21, 3, 22, 0, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 12, 1, 22, 5], [14, 9, 11, 18, 15], [21, 2, 13, 3, 15], [22, 22, 21, 3, 11], [0, 1]]
 g := ![![[21, 18, 21, 8, 18], [21, 7, 0, 21, 3], [1], []], ![[16, 9, 19, 22, 12, 3, 15, 10], [14, 7, 14, 2, 17, 12, 6, 10], [13, 5, 13, 14, 11, 6, 0, 10], [2, 16, 4, 2]], ![[8, 4, 20, 13, 4, 17, 5, 20], [9, 13, 7, 17, 15, 15, 18, 21], [4, 21, 15, 1, 20, 16, 12, 7], [15, 3, 22, 18]], ![[15, 4, 2, 10, 10, 3, 10, 19], [11, 17, 2, 17, 8, 4, 2, 11], [8, 16, 3, 8, 10, 11, 5, 15], [9, 2, 9, 18]], ![[2, 19, 19, 10, 17, 18, 7, 17], [3, 14, 16, 5, 13, 22, 15, 15], [2, 20, 21, 5, 22, 6, 11, 17], [5, 8, 16, 6]]]
 h' := ![![[19, 12, 1, 22, 5], [19, 1, 11, 16, 15], [2, 20, 1, 0, 7], [0, 0, 1], [0, 1]], ![[14, 9, 11, 18, 15], [19, 6, 10, 4, 5], [13, 9, 15, 4, 18], [20, 22, 6, 17, 18], [19, 12, 1, 22, 5]], ![[21, 2, 13, 3, 15], [5, 0, 12, 22, 3], [2, 8, 18, 2, 11], [19, 6, 2, 8, 18], [14, 9, 11, 18, 15]], ![[22, 22, 21, 3, 11], [21, 15, 9, 8, 14], [14, 1, 5, 17, 6], [22, 15, 19, 5, 1], [21, 2, 13, 3, 15]], ![[0, 1], [2, 1, 4, 19, 9], [21, 8, 7, 0, 4], [11, 3, 18, 16, 9], [22, 22, 21, 3, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 15, 2, 20], [], [], []]
 b := ![[], [21, 4, 17, 13, 19], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [21, 3, 22, 0, 16, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6913068761, -5020534738863, 12223425569950, -4946640411911, 2222632817350]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-300568207, -218284119081, 531453285650, -215071322257, 96636209450]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB984I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB984I0 : PrimesBelowBoundCertificateInterval O 1 23 984 where
  m := 9
  g := ![5, 5, 5, 3, 2, 2, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB984I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 7, 7]
    · exact ![14641, 11]
    · exact ![2197, 169]
    · exact ![4913, 289]
    · exact ![6859, 361]
    · exact ![6436343]
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
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
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
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I7N2, I11N1, I13N1, I17N1, I19N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N1], [I13N1], [I17N1], [I19N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
