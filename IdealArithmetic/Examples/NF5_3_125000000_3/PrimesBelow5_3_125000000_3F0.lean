
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66, 48, -20, -14, -61]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![66, 48, -20, -14, -61]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![66, 48, -20, -14, -61], ![92, 68, -29, -20, -88], ![128, 91, -36, -26, -112], ![42, 35, -16, -10, -48], ![-25, -18, 7, 5, 22]]]
  hmulB := by decide  
  f := ![![![0, 4, -5, -3, -16]], ![![4, -6, 4, 3, 14]], ![![-16, 7, 4, 0, 4]], ![![6, 7, -15, -7, -47]], ![![7, -6, 2, 2, 10]]]
  g := ![![![40, 48, -20, -14, -61], ![56, 68, -29, -20, -88], ![77, 91, -36, -26, -112], ![26, 35, -16, -10, -48], ![-15, -18, 7, 5, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, 4, 2, 7]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-5, -1, 4, 2, 7]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-5, -1, 4, 2, 7], ![-20, -11, 22, 12, 40], ![-128, -66, 141, 76, 272], ![-358, -166, 372, 199, 692], ![103, 50, -110, -59, -209]]]
  hmulB := by decide  
  f := ![![![55, 43, -20, -13, -59]], ![![38, 23, -6, -6, -22]], ![![56, 58, -39, -20, -104]], ![![13, -21, 36, 12, 83]], ![![17, 13, -6, -4, -18]]]
  g := ![![![-6, -1, 4, 2, 7], ![-30, -11, 22, 12, 40], ![-200, -66, 141, 76, 272], ![-525, -166, 372, 199, 692], ![156, 50, -110, -59, -209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -25, 30, 12, 74]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-3, -25, 30, 12, 74]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-3, -25, 30, 12, 74], ![8, 95, -111, -44, -272], ![-32, -355, 415, 162, 1008], ![68, 621, -734, -283, -1772], ![-2, 22, -23, -10, -59]]]
  hmulB := by decide  
  f := ![![![-158, -115, 49, 34, 148]], ![![-191, -139, 61, 42, 182]], ![![-247, -176, 87, 58, 246]], ![![-171, -115, 83, 51, 202]], ![![-37, -30, 3, 4, 23]]]
  g := ![![![-47, -25, 30, 12, 74], ![170, 95, -111, -44, -272], ![-631, -355, 415, 162, 1008], ![1118, 621, -734, -283, -1772], ![34, 22, -23, -10, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![66, 48, -20, -14, -61]] ![![-5, -1, 4, 2, 7]]
  ![![-1, 0, 2, 1, 3]] where
 M := ![![![-1, 0, 2, 1, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-1, 0, 2, 1, 3]] ![![-5, -1, 4, 2, 7]]
  ![![-300, -147, 320, 172, 602]] where
 M := ![![![-300, -147, 320, 172, 602]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-300, -147, 320, 172, 602]] ![![-3, -25, 30, 12, 74]]
  ![![-24, -9, 23, 12, 42]] where
 M := ![![![-24, -9, 23, 12, 42]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-24, -9, 23, 12, 42]] ![![-3, -25, 30, 12, 74]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-4, -44, 50, 18, 114]]]
 hmul := by decide  
 g := ![![![![-2, -22, 25, 9, 57]]]]
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
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 5 2 1 [2, 0, 1, 2, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 1], [0, 2, 2, 2, 1], [2, 0, 0, 0, 1], [2, 0, 1, 0, 1], [0, 1]]
 g := ![![[]], ![[0, 2, 2, 1, 1]], ![[2, 0, 2, 2, 1, 2, 1, 1]], ![[0, 0, 1, 0, 2, 2, 1, 1]], ![[1, 1, 1, 0, 2, 2, 1, 1]]]
 h' := ![![[0, 0, 0, 1], [0, 1]], ![[0, 2, 2, 2, 1], [0, 0, 0, 1]], ![[2, 0, 0, 0, 1], [0, 2, 2, 2, 1]], ![[2, 0, 1, 0, 1], [2, 0, 0, 0, 1]], ![[0, 1], [2, 0, 1, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], [], [], []]
 b := ![[], [0, 2, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 5
  hpos := by decide
  P := [2, 0, 1, 2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42624307697009235, 20876865137315268, -45440499211906527, -24418497678480477, -85423158159179847]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14208102565669745, 6958955045771756, -15146833070635509, -8139499226160159, -28474386053059949]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 243 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, -2, -1, -3]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![2, 1, -2, -1, -3]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 1, -2, -1, -3], ![12, 7, -14, -8, -28], ![80, 38, -85, -44, -160], ![202, 92, -206, -113, -378], ![-61, -27, 62, 33, 114]]]
  hmulB := by decide  
  f := ![![![-532, -387, 162, 113, 493]], ![![-148, -109, 46, 32, 140]], ![![-208, -150, 63, 44, 192]], ![![-70, -52, 22, 15, 66]], ![![-65, -48, 20, 14, 61]]]
  g := ![![![1, 1, -2, -1, -3], ![8, 7, -14, -8, -28], ![48, 38, -85, -44, -160], ![116, 92, -206, -113, -378], ![-35, -27, 62, 33, 114]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![2, 1, -2, -1, -3]] ![![2, 1, -2, -1, -3]]
  ![![-163, -78, 172, 92, 322]] where
 M := ![![![-163, -78, 172, 92, 322]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-163, -78, 172, 92, 322]] ![![2, 1, -2, -1, -3]]
  ![![11440, 5597, -12190, -6551, -22915]] where
 M := ![![![11440, 5597, -12190, -6551, -22915]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![11440, 5597, -12190, -6551, -22915]] ![![2, 1, -2, -1, -3]]
  ![![-810643, -396588, 863688, 464212, 1623332]] where
 M := ![![![-810643, -396588, 863688, 464212, 1623332]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-810643, -396588, 863688, 464212, 1623332]] ![![2, 1, -2, -1, -3]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![57462270, 28110925, -61221050, -32904925, -115065975]]]
 hmul := by decide  
 g := ![![![![11492454, 5622185, -12244210, -6580985, -23013195]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [6, 0, 1, 0, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4, 6, 3], [6, 4, 1, 1], [2, 1, 4, 4, 2], [1, 4, 3, 6, 5], [0, 1]]
 g := ![![[2, 4, 1], []], ![[2, 0, 1, 0, 0, 6, 6], [2, 3, 0, 4, 6]], ![[3, 0, 2, 1, 2], [0, 4, 1, 0, 1]], ![[4, 4, 1, 5, 2, 3, 3, 2], [2, 3, 2, 1, 2, 2, 3, 1]], ![[0, 1, 3, 3, 2, 2, 1, 3], [6, 4, 4, 5, 4, 1, 5, 6]]]
 h' := ![![[2, 4, 6, 3], [0, 0, 0, 1], [0, 1]], ![[6, 4, 1, 1], [3, 2, 5, 4, 4], [2, 4, 6, 3]], ![[2, 1, 4, 4, 2], [6, 2, 5, 4], [6, 4, 1, 1]], ![[1, 4, 3, 6, 5], [3, 1, 5, 4, 6], [2, 1, 4, 4, 2]], ![[0, 1], [0, 2, 6, 1, 4], [1, 4, 3, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 3, 5], [], [], []]
 b := ![[], [1, 0, 6, 2, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [6, 0, 1, 0, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20575581134781723698039, 10095572216032375770684, -21955252605520514193396, -11794739731579730754381, -41285735197585094466376]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2939368733540246242577, 1442224602290339395812, -3136464657931502027628, -1684962818797104393483, -5897962171083584923768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 76, -91, -35, -219]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![10, 76, -91, -35, -219]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![7, 5, 3, 1, 0], ![2, 9, 3, 0, 1]] where
  M :=![![![10, 76, -91, -35, -219], ![-36, -292, 349, 134, 844], ![160, 1143, -1376, -534, -3320], ![-214, -2029, 2405, 925, 5846], ![-21, -58, 77, 31, 178]]]
  hmulB := by decide  
  f := ![![![-308, -224, 93, 65, 283]], ![![-428, -318, 135, 94, 412]], ![![-608, -431, 182, 126, 552]], ![![-574, -418, 175, 122, 533]], ![![-561, -411, 174, 121, 530]]]
  g := ![![![63, 202, 61, -35, -219], ![-242, -778, -235, 134, 844], ![958, 3063, 926, -534, -3320], ![-1671, -5388, -1628, 925, 5846], ![-54, -165, -50, 31, 178]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 3, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 8, 1], [2, 2, 10], [0, 1]]
 g := ![![[9, 2, 3], [2, 4, 1], []], ![[5, 10, 0, 4], [3, 2, 9, 4], [9, 1]], ![[8, 5, 4, 2], [8, 10, 2, 2], [0, 1]]]
 h' := ![![[2, 8, 1], [9, 1, 6], [0, 0, 1], [0, 1]], ![[2, 2, 10], [3, 10, 2], [6, 4, 2], [2, 8, 1]], ![[0, 1], [2, 0, 3], [4, 7, 8], [2, 2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 3], []]
 b := ![[], [8, 4, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 3, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1596893220, 822572203, -1748185107, -931607588, -3314230649]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1340600694, 3209880544, 999029964, -931607588, -3314230649]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![308, 224, -93, -65, -283]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![308, 224, -93, -65, -283]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![2, 5, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 6, 0, 0, 1]] where
  M :=![![![308, 224, -93, -65, -283], ![428, 318, -135, -94, -412], ![608, 431, -182, -126, -552], ![194, 147, -53, -39, -166], ![-121, -82, 33, 23, 100]]]
  hmulB := by decide  
  f := ![![![-10, -76, 91, 35, 219]], ![![36, 292, -349, -134, -844]], ![![0, 15, -17, -6, -42]], ![![14, 143, -169, -65, -412]], ![![17, 130, -156, -60, -377]]]
  g := ![![![209, 217, -93, -65, -283], ![302, 315, -135, -94, -412], ![408, 423, -182, -126, -552], ![124, 128, -53, -39, -166], ![-75, -77, 33, 23, 100]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [7, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[7, 3], [0, 3], [1]], ![[3, 8], [7, 8], [1]]]
 h' := ![![[6, 10], [0, 6], [4, 6], [0, 1]], ![[0, 1], [3, 5], [7, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [9, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [7, 5, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-680131, -515557, 929333, 468256, 1870046]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1336233, -1489318, 929333, 468256, 1870046]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![10, 76, -91, -35, -219]] ![![308, 224, -93, -65, -283]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![550, 407, -182, -123, -541]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![550, 407, -182, -123, -541]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![6, 6, 0, 4, 1]] where
  M :=![![![550, 407, -182, -123, -541], ![788, 541, -234, -168, -692], ![1264, 978, -663, -388, -1696], ![870, 324, -442, -291, -830], ![-363, -233, 234, 135, 518]]]
  hmulB := by decide  
  f := ![![![92, -29, -42, -13, -101]], ![![-92, -107, 210, 112, 628]], ![![-176, 502, -471, -300, -1536]], ![![574, -492, 122, 145, 574]], ![![173, -227, 134, 101, 478]]]
  g := ![![![292, 281, -14, 157, -541], ![380, 361, -18, 200, -692], ![880, 858, -51, 492, -1696], ![450, 408, -34, 233, -830], ![-267, -257, 18, -149, 518]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [5, 1, 1, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 5, 10, 11], [9, 8, 1, 3], [0, 12, 2, 12], [0, 1]]
 g := ![![[0, 6, 8, 12], [2, 9, 1], []], ![[6, 1, 11, 7, 3, 6], [9, 10, 1], [2, 1, 6, 4, 9, 5]], ![[2, 3, 8, 12, 5, 4], [8, 1, 10], [1, 10, 5, 2, 10, 1]], ![[0, 7, 1, 1, 4, 1], [12, 8, 10], [3, 10, 6, 11, 10, 12]]]
 h' := ![![[0, 5, 10, 11], [3, 5, 10, 8], [0, 0, 0, 1], [0, 1]], ![[9, 8, 1, 3], [3, 3, 9, 6], [3, 6, 6, 12], [0, 5, 10, 11]], ![[0, 12, 2, 12], [2, 1, 8, 7], [9, 8, 11, 6], [9, 8, 1, 3]], ![[0, 1], [9, 4, 12, 5], [11, 12, 9, 7], [0, 12, 2, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 7, 12], []]
 b := ![[], [], [12, 1, 9, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [5, 1, 1, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-676432026115, -700200374654, 1138263710948, 541242488002, 2393006722940]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1156497874135, -1158326208638, 87558746996, -694675723366, 2393006722940]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![92, -29, -42, -13, -101]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![92, -29, -42, -13, -101]] 
 ![![13, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![92, -29, -42, -13, -101], ![-92, -107, 210, 112, 628], ![-176, 502, -471, -300, -1536], ![574, -492, 122, 145, 574], ![-47, -167, 246, 139, 756]]]
  hmulB := by decide  
  f := ![![![550, 407, -182, -123, -541]], ![![526, 386, -172, -117, -511]], ![![478, 357, -177, -115, -505]], ![![490, 338, -174, -117, -480]], ![![99, 76, -24, -18, -85]]]
  g := ![![![94, -29, -42, -13, -101], ![-293, -107, 210, 112, 628], ![473, 502, -471, -300, -1536], ![132, -492, 122, 145, 574], ![-314, -167, 246, 139, 756]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![550, 407, -182, -123, -541]] ![![92, -29, -42, -13, -101]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -3, 6, 3, 17]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-6, -3, 6, 3, 17]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![15, 16, 2, 1, 0], ![2, 15, 10, 0, 1]] where
  M :=![![![-6, -3, 6, 3, 17], ![-4, 11, -14, -8, -44], ![16, -42, 31, 20, 96], ![-46, 20, 10, 3, 14], ![-1, 17, -18, -11, -54]]]
  hmulB := by decide  
  f := ![![![-4, -3, 2, 1, 5]], ![![-4, -1, -2, 0, -4]], ![![-16, -22, 27, 12, 64]], ![![-10, -5, 2, 2, 5]], ![![-13, -14, 14, 7, 34]]]
  g := ![![![-5, -18, -10, 3, 17], ![12, 47, 26, -8, -44], ![-28, -106, -57, 20, 96], ![-7, -14, -8, 3, 14], ![16, 59, 32, -11, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [3, 14, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 4, 5], [14, 12, 12], [0, 1]]
 g := ![![[14, 14, 1], [11, 8], [6, 1], []], ![[15, 5, 2, 3], [13, 1], [5, 8], [3, 8]], ![[2, 12, 4, 12], [1, 16], [14, 16], [13, 8]]]
 h' := ![![[9, 4, 5], [2, 13, 16], [16, 15, 5], [0, 0, 1], [0, 1]], ![[14, 12, 12], [13, 12, 2], [1, 5, 16], [4, 6, 12], [9, 4, 5]], ![[0, 1], [10, 9, 16], [8, 14, 13], [4, 11, 4], [14, 12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 6], []]
 b := ![[], [12, 1, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [3, 14, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141154399, -67898046, 149114750, 80342270, 279521028]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-112078265, -326246458, -165104710, 80342270, 279521028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -3, 2, 1, 5]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-4, -3, 2, 1, 5]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![11, 13, 1, 0, 0], ![5, 15, 0, 1, 0], ![4, 15, 0, 0, 1]] where
  M :=![![![-4, -3, 2, 1, 5], ![-4, -1, -2, 0, -4], ![-16, -22, 27, 12, 64], ![-14, 20, -18, -5, -54], ![7, 3, -6, -3, -12]]]
  hmulB := by decide  
  f := ![![![-6, -3, 6, 3, 17]], ![![-4, 11, -14, -8, -44]], ![![-6, 4, -5, -3, -17]], ![![-8, 10, -10, -6, -33]], ![![-5, 10, -12, -7, -38]]]
  g := ![![![-3, -7, 2, 1, 5], ![2, 5, -2, 0, -4], ![-37, -89, 27, 12, 64], ![25, 67, -18, -5, -54], ![8, 18, -6, -3, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 16], [0, 1]]
 g := ![![[1, 8], [1], [4], [1]], ![[0, 9], [1], [4], [1]]]
 h' := ![![[2, 16], [10, 12], [12, 16], [2, 2], [0, 1]], ![[0, 1], [0, 5], [10, 1], [6, 15], [2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [3, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [15, 15, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71322, -41545, 83330, 43667, 160807]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-108795, -246585, 83330, 43667, 160807]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-6, -3, 6, 3, 17]] ![![-4, -3, 2, 1, 5]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 0, 3, 1, 7]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-4, 0, 3, 1, 7]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![4, 10, 1, 0, 0], ![18, 0, 0, 1, 0], ![6, 12, 0, 0, 1]] where
  M :=![![![-4, 0, 3, 1, 7], ![4, 8, -13, -6, -36], ![0, -39, 44, 22, 120], ![-26, 49, -37, -17, -106], ![5, 8, -13, -7, -36]]]
  hmulB := by decide  
  f := ![![![-62, -44, 19, 13, 57]], ![![-84, -62, 25, 18, 76]], ![![-64, -47, 20, 14, 60]], ![![-62, -43, 19, 13, 56]], ![![-71, -52, 21, 15, 64]]]
  g := ![![![-4, -6, 3, 1, 7], ![20, 30, -13, -6, -36], ![-68, -101, 44, 22, 120], ![56, 89, -37, -17, -106], ![21, 30, -13, -7, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [5, 0, 1] where
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
 g := ![![[0, 4], [], [], [1]], ![[0, 15], [], [], [1]]]
 h' := ![![[0, 18], [0, 17], [6], [14], [0, 1]], ![[0, 1], [0, 2], [6], [14], [0, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [5, 0, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1583406, -1047094, 1992606, 1023531, 3927610]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2712792, -3584446, 1992606, 1023531, 3927610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -7, 8, 3, 19]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![0, -7, 8, 3, 19]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![0, -7, 8, 3, 19], ![4, 27, -32, -12, -76], ![-16, -104, 127, 48, 304], ![30, 194, -236, -91, -570], ![1, 3, -4, -1, -8]]]
  hmulB := by decide  
  f := ![![![30, 15, -8, -5, -19]], ![![26, 14, -8, -5, -19]], ![![14, 7, -9, -5, -19]], ![![30, 14, -20, -11, -38]], ![![-1, 0, 4, 2, 7]]]
  g := ![![![0, -7, 8, 3, 19], ![1, 27, -32, -12, -76], ![-7, -104, 127, 48, 304], ![14, 194, -236, -91, -570], ![0, 3, -4, -1, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, 13, -6, -5, -23]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-12, 13, -6, -5, -23]] 
 ![![19, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-12, 13, -6, -5, -23], ![28, -15, -6, 0, -12], ![-48, -26, 69, 36, 192], ![-62, 60, -34, -27, -162], ![39, -3, -26, -11, -60]]]
  hmulB := by decide  
  f := ![![![8454, 6175, -2598, -1809, -7905]], ![![7740, 5653, -2378, -1656, -7236]], ![![5316, 3884, -1635, -1138, -4974]], ![![3408, 2487, -1044, -728, -3179]], ![![7393, 5400, -2272, -1582, -6913]]]
  g := ![![![14, 13, -6, -5, -23], ![28, -15, -6, 0, -12], ![-202, -26, 69, 36, 192], ![119, 60, -34, -27, -162], ![76, -3, -26, -11, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2

def I19N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 2, -4, -2, -8]] i)))

def SI19N3: IdealEqSpanCertificate' Table ![![3, 2, -4, -2, -8]] 
 ![![19, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![3, 2, -4, -2, -8], ![16, 5, -14, -8, -24], ![96, 58, -115, -60, -224], ![264, 110, -260, -143, -476], ![-76, -38, 82, 44, 155]]]
  hmulB := by decide  
  f := ![![![-31, -54, 24, 18, 80]], ![![-32, -47, 22, 16, 72]], ![![-18, -30, 9, 8, 32]], ![![-11, -28, 16, 11, 52]], ![![-8, -10, 6, 4, 19]]]
  g := ![![![3, 2, -4, -2, -8], ![12, 5, -14, -8, -24], ![86, 58, -115, -60, -224], ![211, 110, -260, -143, -476], ![-64, -38, 82, 44, 155]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N3 : Nat.card (O ⧸ I19N3) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N3)

lemma isPrimeI19N3 : Ideal.IsPrime I19N3 := prime_ideal_of_norm_prime hp19.out _ NI19N3
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-4, 0, 3, 1, 7]] ![![0, -7, 8, 3, 19]]
  ![![-11, -69, 85, 34, 210]] where
 M := ![![![-11, -69, 85, 34, 210]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-11, -69, 85, 34, 210]] ![![-12, 13, -6, -5, -23]]
  ![![202, 92, -271, -113, -707]] where
 M := ![![![202, 92, -271, -113, -707]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N2 : IdealMulLeCertificate' Table 
  ![![202, 92, -271, -113, -707]] ![![3, 2, -4, -2, -8]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-38, -418, 475, 171, 1083]]]
 hmul := by decide  
 g := ![![![![-2, -22, 25, 9, 57]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2, I19N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
    exact isPrimeI19N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1 ⊙ MulI19N2)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54, 12, 17, 1, 31]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![54, 12, 17, 1, 31]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![17, 16, 7, 1, 0], ![19, 11, 7, 0, 1]] where
  M :=![![![54, 12, 17, 1, 31], ![100, 176, -169, -74, -420], ![96, -343, 452, 158, 1096], ![246, 877, -1079, -439, -2554], ![-51, -10, 15, 13, 22]]]
  hmulB := by decide  
  f := ![![![-76, 32, 25, 5, 53]], ![![92, 66, -159, -82, -468]], ![![96, -381, 390, 242, 1256]], ![![18, -28, 20, 14, 69]], ![![13, -53, 55, 34, 177]]]
  g := ![![![-24, -15, -9, 1, 31], ![406, 260, 143, -74, -420], ![-1018, -649, -362, 158, 1096], ![2445, 1565, 864, -439, -2554], ![-30, -20, -10, 13, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [10, 20, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 11, 16], [16, 11, 7], [0, 1]]
 g := ![![[21, 7, 12], [13, 14, 6], [11, 13, 1], []], ![[7, 0, 0, 13], [21, 6, 17, 9], [19, 9, 21, 4], [0, 3]], ![[22, 12, 3, 20], [18, 15, 19, 22], [19, 4, 9, 19], [9, 3]]]
 h' := ![![[20, 11, 16], [8, 16, 9], [5, 18, 11], [0, 0, 1], [0, 1]], ![[16, 11, 7], [18, 2, 10], [4, 16, 18], [9, 19, 11], [20, 11, 16]], ![[0, 1], [10, 5, 4], [3, 12, 17], [5, 4, 11], [16, 11, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 17], []]
 b := ![[], [19, 13, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [10, 20, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1436446736, -778957578, 1616689712, 854180626, 3090916050]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3247170536, -2106344528, -1130390740, 854180626, 3090916050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![150, 109, -48, -33, -143]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![150, 109, -48, -33, -143]] 
 ![![23, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![150, 109, -48, -33, -143], ![220, 157, -78, -52, -220], ![368, 250, -175, -108, -432], ![322, 180, -268, -149, -538], ![-121, -73, 86, 49, 182]]]
  hmulB := by decide  
  f := ![![![-16, -101, 140, 83, 443]], ![![-20, -52, 82, 47, 255]], ![![32, -41, 25, 21, 97]], ![![-30, -23, 52, 24, 143]], ![![-25, -58, 94, 54, 293]]]
  g := ![![![53, 109, -48, -33, -143], ![89, 157, -78, -52, -220], ![215, 250, -175, -108, -432], ![359, 180, -268, -149, -538], ![-113, -73, 86, 49, 182]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 6, -2, -2, -10]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-7, 6, -2, -2, -10]] 
 ![![23, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-7, 6, -2, -2, -10], ![8, -11, 4, 4, 8], ![-64, -32, 77, 40, 176], ![-132, -16, 86, 43, 108], ![50, 12, -44, -22, -87]]]
  hmulB := by decide  
  f := ![![![3947, 2878, -1206, -842, -3674]], ![![3157, 2303, -966, -674, -2942]], ![![2050, 1492, -623, -436, -1900]], ![![1830, 1340, -566, -393, -1720]], ![![-66, -48, 20, 14, 61]]]
  g := ![![![-3, 6, -2, -2, -10], ![5, -11, 4, 4, 8], ![-30, -32, 77, 40, 176], ![-50, -16, 86, 43, 108], ![22, 12, -44, -22, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![54, 12, 17, 1, 31]] ![![150, 109, -48, -33, -143]]
  ![![13567, 9937, -4105, -2872, -12602]] where
 M := ![![![13567, 9937, -4105, -2872, -12602]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![13567, 9937, -4105, -2872, -12602]] ![![-7, 6, -2, -2, -10]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-3749, -1817, 4025, 2162, 7544]]]
 hmul := by decide  
 g := ![![![![-163, -79, 175, 94, 328]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB547I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB547I0 : PrimesBelowBoundCertificateInterval O 1 23 547 where
  m := 9
  g := ![5, 1, 5, 1, 2, 2, 2, 4, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB547I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2, I19N3]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![243]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![1331, 121]
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![361, 19, 19, 19]
    · exact ![12167, 23, 23]
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
      exact NI19N2
      exact NI19N3
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I11N1, I13N1, I17N1, I19N0, I19N1, I19N2, I19N3, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1], [I13N1], [I17N1], [I19N0, I19N1, I19N2, I19N3], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
