
import IdealArithmetic.Examples.NF5_1_25312500_1.RI5_1_25312500_1
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [6, 22, 0, 18, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 19, 25, 7, 20], [3, 21, 7, 5, 24], [25, 15, 2, 25, 5], [16, 2, 24, 21, 9], [0, 1]]
 g := ![![[27, 4, 26, 18, 13], [14, 4, 20, 7], [15, 27, 1], []], ![[11, 5, 22, 4, 22, 28, 21, 6], [8, 12, 0, 22], [14, 5, 22, 15, 25, 2, 13, 9], [28, 19, 27, 5, 13, 14, 27, 25]], ![[28, 28, 21, 20, 1, 21, 8, 5], [25, 21, 0, 13], [8, 18, 14, 15, 13, 25, 1, 16], [1, 15, 15, 17, 5, 19, 16, 20]], ![[8, 3, 1, 17, 7, 18, 10, 13], [12, 18, 11, 16], [28, 14, 4, 6, 24, 20, 11, 24], [4, 16, 28, 19, 3, 23, 1, 9]], ![[9, 27, 6, 25, 3, 25, 19, 25], [12, 26, 23, 4], [16, 22, 7, 12, 27, 15, 19, 6], [11, 8, 9, 14, 15, 24, 20, 4]]]
 h' := ![![[12, 19, 25, 7, 20], [12, 10, 0, 21, 19], [26, 1, 9, 27, 6], [0, 0, 0, 1], [0, 1]], ![[3, 21, 7, 5, 24], [10, 13, 4, 22, 26], [0, 23, 9, 15, 15], [23, 25, 16, 6, 12], [12, 19, 25, 7, 20]], ![[25, 15, 2, 25, 5], [25, 23, 25, 16, 12], [28, 13, 15, 10, 10], [21, 20, 26, 21, 22], [3, 21, 7, 5, 24]], ![[16, 2, 24, 21, 9], [19, 4, 0, 0, 22], [2, 7, 9, 20, 25], [28, 14, 8, 8, 17], [25, 15, 2, 25, 5]], ![[0, 1], [6, 8, 0, 28, 8], [7, 14, 16, 15, 2], [28, 28, 8, 22, 7], [16, 2, 24, 21, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 10, 0, 2], [], [], []]
 b := ![[], [0, 10, 15, 11, 26], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [6, 22, 0, 18, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18153603831, -230366040066, 218978386824, -137067386226, -851561653753]
  a := ![45, -18, 66, -24, -205]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-625986339, -7943656554, 7550978856, -4726461594, -29364194957]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 6, -3, 3, 16]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![13, 6, -3, 3, 16]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![17, 21, 7, 1, 0], ![17, 10, 14, 0, 1]] where
  M :=![![![13, 6, -3, 3, 16], ![-6, 34, -27, 18, 102], ![-18, 120, -146, 81, 558], ![72, 183, -131, 97, 540], ![-12, 27, -42, 21, 157]]]
  hmulB := by decide  
  f := ![![![7, 3, -3, 0, 8]], ![![24, 7, 27, -9, -72]], ![![-54, -39, 34, 0, -90]], ![![5, -3, 21, -5, -56]], ![![-13, -14, 23, -3, -61]]]
  g := ![![![-10, -7, -8, 3, 16], ![-66, -44, -51, 18, 102], ![-351, -231, -275, 81, 558], ![-347, -234, -270, 97, 540], ![-98, -64, -77, 21, 157]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [7, 19, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 21, 18], [18, 9, 13], [0, 1]]
 g := ![![[21, 2, 8], [0, 7, 20], [3, 3, 25], [1]], ![[9, 27, 3, 18], [21, 28, 5, 2], [5, 0, 6, 20], [2, 17, 25, 4]], ![[1, 3, 9, 6], [4, 6, 23, 30], [8, 1, 4, 23], [11, 17, 26, 27]]]
 h' := ![![[8, 21, 18], [0, 20, 15], [10, 2, 19], [24, 12, 26], [0, 1]], ![[18, 9, 13], [18, 29, 30], [28, 20, 21], [2, 0, 16], [8, 21, 18]], ![[0, 1], [28, 13, 17], [14, 9, 22], [20, 19, 20], [18, 9, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 26], []]
 b := ![[], [6, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [7, 19, 5, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-236977328, -5510561064, 5548605272, -3379928640, -21228258280]
  a := ![537, -240, 776, -300, -2446]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13487167752, 8959694296, 10529152312, -3379928640, -21228258280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![790339, 331143, 251390, -155591, -643670]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![790339, 331143, 251390, -155591, -643670]] 
 ![![31, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![790339, 331143, 251390, -155591, -643670], ![869628, -298798, 2601090, -646149, -6965432], ![-9265614, -3653415, -3749071, 1987929, 9704670], ![-2222904, 1549963, -9404496, 2214716, 25222716], ![-2271018, -1112922, -156662, 331500, 326779]]]
  hmulB := by decide  
  f := ![![![-71627, -223847, 183948, -124847, -738938]], ![![-31366, -131594, 113080, -74827, -449424]], ![![-63651, -279768, 244979, -160554, -971628]], ![![-75250, -370073, 324334, -212282, -1283376]], ![![-48473, -167723, 141370, -94625, -565255]]]
  g := ![![![230653, 331143, 251390, -155591, -643670], ![3212032, -298798, 2601090, -646149, -6965432], ![-3724587, -3653415, -3749071, 1987929, 9704670], ![-11717490, 1549963, -9404496, 2214716, 25222716], ![57161, -1112922, -156662, 331500, 326779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4421, 1874, 529, 431, -324]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![4421, 1874, 529, 431, -324]] 
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![4421, 1874, 529, 431, -324], ![-8730, 7438, -10735, 5466, 38258], ![16386, 29532, -25370, 16989, 103890], ![1956, 45103, -39167, 25597, 152696], ![6864, 6759, -5314, 3789, 22949]]]
  hmulB := by decide  
  f := ![![![-284017, -315453, 598257, -84784, -1622300]], ![![-355137, -303056, 427734, -40563, -1166248]], ![![3681, -27438, 102751, -21480, -276438]], ![![208042, -110878, 760351, -182794, -2038066]], ![![-70742, -56331, 71054, -5189, -194225]]]
  g := ![![![-1940, 1874, 529, 431, -324], ![-14965, 7438, -10735, 5466, 38258], ![-50688, 29532, -25370, 16989, 103890], ![-76188, 45103, -39167, 25597, 152696], ![-11461, 6759, -5314, 3789, 22949]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![13, 6, -3, 3, 16]] ![![790339, 331143, 251390, -155591, -643670]]
  ![![284017, 315453, -598257, 84784, 1622300]] where
 M := ![![![284017, 315453, -598257, 84784, 1622300]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![284017, 315453, -598257, 84784, 1622300]] ![![4421, 1874, 529, 431, -324]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4423763, 16026408, -12794145, 8797187, 51264936]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![4423763, 16026408, -12794145, 8797187, 51264936]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![15, 15, 9, 1, 1]] where
  M :=![![![4423763, 16026408, -12794145, 8797187, 51264936], ![-4554558, 66004072, -67702833, 40792248, 259984910], ![45694266, 280991178, -255431894, 164021733, 1005100146], ![20969748, 397948799, -377431725, 236633305, 1467960264], ![15865956, 67183809, -59066098, 38647503, 234405179]]]
  hmulB := by decide  
  f := ![![![-421615357, -201267979, -47824319, 65372138, 111112096]], ![![-843362196, 35989609, -1632979417, 444876285, 4360506452]], ![![5073746226, 2270771799, 1105849270, -895051686, -2764702698]], ![![2605607418, -397205192, 6047686409, -1579305788, -16170637990]], ![![821995011, 491934004, -255646223, -56165600, 722526637]]]
  g := ![![![-20663521, -20349936, -12815637, -1147777, 51264936], ![-105522384, -103615394, -65069379, -5924126, 259984910], ![-406238052, -399878676, -251387384, -22731849, 1005100146], ![-594552276, -584363653, -367272273, -33279107, 1467960264], ![-94600317, -93213348, -58613857, -5290748, 234405179]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [26, 26, 2, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 4, 12, 15], [9, 15, 3, 1], [4, 17, 22, 21], [0, 1]]
 g := ![![[18, 0, 19, 10], [2, 21, 10], [25, 24, 8, 10], [1], []], ![[16, 35, 29, 28, 29, 31], [36, 20, 12], [11, 30, 29, 32, 16, 23], [23, 23, 1], [28, 31, 3]], ![[24, 3, 25, 26, 29, 34], [14, 22, 26], [8, 0, 8, 22, 5, 4], [26, 13, 25], [18, 32, 1]], ![[30, 15, 28, 8, 16, 9], [20, 4, 27], [26, 34, 18, 11, 12, 26], [17, 25, 36], [1, 32, 34]]]
 h' := ![![[13, 4, 12, 15], [19, 24, 21, 11], [16, 31, 26, 26], [11, 11, 35, 26], [0, 0, 1], [0, 1]], ![[9, 15, 3, 1], [29, 22, 11, 28], [15, 32, 5, 30], [10, 32, 29, 35], [33, 13, 17, 1], [13, 4, 12, 15]], ![[4, 17, 22, 21], [2, 7, 1, 21], [25, 27, 8, 10], [20, 3, 0, 35], [20, 6, 14, 5], [9, 15, 3, 1]], ![[0, 1], [26, 21, 4, 14], [18, 21, 35, 8], [28, 28, 10, 15], [27, 18, 5, 31], [4, 17, 22, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 10, 13], []]
 b := ![[], [], [0, 8, 34, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [26, 26, 2, 11, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25700734, 425065932, -415079488, 256663086, 1601938242]
  a := ![38, -16, 56, -21, -173]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-648739808, -637946154, -400879018, -36358788, 1601938242]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421615357, 201267979, 47824319, -65372138, -111112096]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![421615357, 201267979, 47824319, -65372138, -111112096]] 
 ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![421615357, 201267979, 47824319, -65372138, -111112096], ![843362196, -35989609, 1632979417, -444876285, -4360506452], ![-5073746226, -2270771799, -1105849270, 895051686, 2764702698], ![-2605607418, 397205192, -6047686409, 1579305788, 16170637990], ![-1119155250, -640992699, 247184050, 97082583, -712169621]]]
  hmulB := by decide  
  f := ![![![-4423763, -16026408, 12794145, -8797187, -51264936]], ![![3535, -2217040, 2175594, -1340255, -8412158]], ![![-5539182, -23187618, 19351922, -12992445, -77044266]], ![![-3555779, -21584027, 18845550, -12339540, -74313072]], ![![-3656961, -13510725, 10932649, -7464096, -43744823]]]
  g := ![![![84675728, 201267979, 47824319, -65372138, -111112096], ![1917504706, -35989609, 1632979417, -444876285, -4360506452], ![-1622045019, -2270771799, -1105849270, 895051686, 2764702698], ![-7064215468, 397205192, -6047686409, 1579305788, 16170637990], ![200668293, -640992699, 247184050, 97082583, -712169621]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![4423763, 16026408, -12794145, 8797187, 51264936]] ![![421615357, 201267979, 47824319, -65372138, -111112096]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 7, 4, -3, -10]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![17, 7, 4, -3, -10]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![23, 37, 1, 0, 0], ![17, 16, 0, 1, 0], ![27, 38, 0, 0, 1]] where
  M :=![![![17, 7, 4, -3, -10], ![24, -4, 58, -15, -156], ![-198, -81, -67, 39, 174], ![-60, 25, -204, 50, 544], ![-48, -24, 0, 6, -1]]]
  hmulB := by decide  
  f := ![![![49, -5, 26, -9, -82]], ![![-84, -14, -8, -3, 0]], ![![-47, -18, 9, -9, -52]], ![![-11, -10, 12, -7, -50]], ![![-45, -17, 10, -9, -55]]]
  g := ![![![6, 7, 4, -3, -10], ![77, 98, 58, -15, -156], ![-98, -118, -67, 39, 174], ![-266, -339, -204, 50, 544], ![-3, -2, 0, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [22, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 40], [0, 1]]
 g := ![![[1, 16], [39], [18], [37, 33], [1]], ![[18, 25], [39], [18], [8, 8], [1]]]
 h' := ![![[19, 40], [2, 37], [9, 11], [6, 10], [19, 19], [0, 1]], ![[0, 1], [8, 4], [13, 30], [32, 31], [11, 22], [19, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [25, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [22, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13736, 195745, -244765, 130148, 870795]
  a := ![-232, 100, -337, 125, 1057]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-490442, -632208, -244765, 130148, 870795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29227069, -19079333, 14655992, 859733, -40673722]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-29227069, -19079333, 14655992, 859733, -40673722]] 
 ![![41, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![-29227069, -19079333, 14655992, 859733, -40673722], ![-137496360, -23208938, -164313290, 51705573, 436561604], ![378984498, 224442651, -109574597, -27589713, 310802550], ![476340828, 61952169, 633924184, -192343736, -1686526472], ![58347672, 54284772, -86026552, 9882762, 234010985]]]
  hmulB := by decide  
  f := ![![![49171, 540587, -398998, 283663, 1574350]], ![![1455, 168295, -146006, 95340, 567326]], ![![71105, 235354, -187849, 129308, 754712]], ![![27550, 809909, -680938, 451958, 2655524]], ![![1161408, 2206962, -1490780, 1132068, 6223489]]]
  g := ![![![2321002, -19079333, 14655992, 859733, -992042], ![-42173522, -23208938, -164313290, 51705573, 10647844], ![-11780870, 224442651, -109574597, -27589713, 7580550], ![160827051, 61952169, 633924184, -192343736, -41134792], ![-17554480, 54284772, -86026552, 9882762, 5707585]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [22, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 40], [0, 1]]
 g := ![![[18, 25], [33], [39], [37, 32], [1]], ![[40, 16], [33], [39], [34, 9], [1]]]
 h' := ![![[14, 40], [16, 5], [39, 22], [6, 11], [19, 14], [0, 1]], ![[0, 1], [4, 36], [19, 19], [37, 30], [10, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [10, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [22, 27, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6806, 19898, -24659, 10611, 81918]
  a := ![97, -38, 146, -47, -442]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13435, 19898, -24659, 10611, 1998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![237601, 1019506, -965978, 609820, 3817312]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![237601, 1019506, -965978, 609820, 3817312]] 
 ![![41, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![237601, 1019506, -965978, 609820, 3817312], ![475176, 4506341, -3993698, 2590446, 15649432], ![320268, 18608298, -18487405, 11332920, 71571684], ![3574164, 26550236, -24221830, 15511355, 95051428], ![-202680, 4419906, -4606064, 2758134, 17714713]]]
  hmulB := by decide  
  f := ![![![1955895905, 317744850, 2380846586, -744399208, -6327157720]], ![![1151875659, 129858839, 1602875808, -479410530, -4266574976]], ![![-64851891, 9220596, -148190047, 38831220, 396196716]], ![![619374229, 314902066, 2855016, -82263213, 18206020]], ![![1057336202, 157832082, 1335912396, -412395934, -3551897343]]]
  g := ![![![-2889151, 1019506, -965978, 609820, 3817312], ![-12066547, 4506341, -3993698, 2590446, 15649432], ![-53851557, 18608298, -18487405, 11332920, 71571684], ![-72734981, 26550236, -24221830, 15511355, 95051428], ![-13205518, 4419906, -4606064, 2758134, 17714713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![17, 7, 4, -3, -10]] ![![-29227069, -19079333, 14655992, 859733, -40673722]]
  ![![-1955895905, -317744850, -2380846586, 744399208, 6327157720]] where
 M := ![![![-1955895905, -317744850, -2380846586, 744399208, 6327157720]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-1955895905, -317744850, -2380846586, 744399208, 6327157720]] ![![237601, 1019506, -965978, 609820, 3817312]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39041, 272226, -313990, 179496, 1196022]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-39041, 272226, -313990, 179496, 1196022]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![6, 39, 8, 1, 0], ![11, 39, 20, 0, 1]] where
  M :=![![![-39041, 272226, -313990, 179496, 1196022], ![357138, 1217431, -986100, 673494, 3954474], ![-259470, 5071596, -5103485, 3103146, 19636242], ![1017366, 7154184, -6601540, 4205953, 25910598], ![-211464, 1211982, -1290294, 762156, 4908817]]]
  hmulB := by decide  
  f := ![![![-10689203, -4074210, -4817642, 2394000, 12521610]], ![![-5527170, 6068797, -31147380, 7093074, 83613510]], ![![123165198, 44124348, 65396329, -29604474, -170889522]], ![![16566606, 12493269, -14191260, 714907, 38893488]], ![![50288267, 25316949, 1110184, -6858594, -886295]]]
  g := ![![![-331913, -1241232, -596986, 179496, 1196022], ![-1097280, -4169147, -1987524, 673494, 3954474], ![-5462256, -20506152, -9829151, 3103146, 19636242], ![-7191510, -27148635, -12987468, 4205953, 25910598], ![-1367009, -5115255, -2454974, 762156, 4908817]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [14, 6, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 28, 22], [17, 14, 21], [0, 1]]
 g := ![![[3, 2, 4], [8, 7, 4], [30, 15], [17, 18, 1], []], ![[25, 0, 31, 20], [9, 20, 27, 3], [40, 38], [18, 12, 11, 12], [11, 11]], ![[4, 13, 36, 4], [12, 28, 31, 9], [30, 9], [40, 41, 16, 38], [12, 11]]]
 h' := ![![[1, 28, 22], [17, 39, 41], [23, 27, 41], [20, 33, 12], [0, 0, 1], [0, 1]], ![[17, 14, 21], [18, 1, 13], [12, 9, 7], [23, 31, 34], [19, 8, 14], [1, 28, 22]], ![[0, 1], [8, 3, 32], [25, 7, 38], [12, 22, 40], [35, 35, 28], [17, 14, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 18], []]
 b := ![[], [20, 27, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [14, 6, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![256262, -254060, 1117484, -232824, -3105176]
  a := ![-36, 14, -52, 8, 164]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![832794, 3021580, 1513572, -232824, -3105176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10689203, -4074210, -4817642, 2394000, 12521610]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-10689203, -4074210, -4817642, 2394000, 12521610]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![29, 19, 1, 0, 0], ![17, 4, 0, 1, 0], ![5, 12, 0, 0, 1]] where
  M :=![![![-10689203, -4074210, -4817642, 2394000, 12521610], ![-5527170, 6068797, -31147380, 7093074, 83613510], ![123165198, 44124348, 65396329, -29604474, -170889522], ![6737322, -28022040, 110258860, -23417093, -296520390], ![32232384, 14275074, 7553214, -5793948, -18984845]]]
  hmulB := by decide  
  f := ![![![-39041, 272226, -313990, 179496, 1196022]], ![![357138, 1217431, -986100, 673494, 3954474]], ![![125441, 839473, -766165, 490812, 3010602]], ![![41447, 387250, -369390, 231427, 1443276]], ![![90209, 399588, -341708, 226548, 1356805]]]
  g := ![![![598055, -1683124, -4817642, 2394000, 12521610], ![8351094, -10089893, -31147380, 7093074, 83613510], ![-9665225, 22574099, 65396329, -29604474, -170889522], ![-30466909, 35557504, 110258860, -23417093, -296520390], ![153733, 2831580, 7553214, -5793948, -18984845]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [23, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 42], [0, 1]]
 g := ![![[41, 15], [24, 35], [35], [18, 9], [1]], ![[0, 28], [0, 8], [35], [2, 34], [1]]]
 h' := ![![[3, 42], [7, 12], [10, 11], [16, 32], [20, 3], [0, 1]], ![[0, 1], [0, 31], [0, 32], [26, 11], [29, 40], [3, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [1, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [23, 40, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3341, 9332, -6066, 4443, 26653]
  a := ![-10, 7, -8, 12, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-687, -4954, -6066, 4443, 26653]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-39041, 272226, -313990, 179496, 1196022]] ![![-10689203, -4074210, -4817642, 2394000, 12521610]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4103, -556, 6583, -2453, -26098]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-4103, -556, 6583, -2453, -26098]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![30, 3, 7, 26, 1]] where
  M :=![![![-4103, -556, 6583, -2453, -26098], ![-34140, -21274, -12619, -2328, 33736], ![143112, -50436, 142790, -58809, -494520], ![-141666, -89517, 17949, -33637, -123886], ![67536, -9687, 53020, -19047, -177881]]]
  hmulB := by decide  
  f := ![![![-5557, 7549, -36389, 8168, 97722]], ![![146142, 51619, 80179, -35655, -209722]], ![![12624, -103443, 385138, -80358, -1036212]], ![![-554064, -183294, -347471, 144064, 912184]], ![![-297714, -108927, -150119, 69934, 391655]]]
  g := ![![![16571, 1654, 4027, 14385, -26098], ![-22260, -2606, -5293, -18712, 33736], ![318696, 30492, 76690, 272313, -494520], ![76062, 6003, 18833, 67817, -123886], ![114978, 11148, 27621, 97997, -177881]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [17, 20, 41, 44, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 17, 37, 24], [44, 17, 35, 17], [21, 12, 22, 6], [0, 1]]
 g := ![![[23, 46, 3, 28], [23, 10, 26, 24], [24, 43, 4, 37], [3, 1], []], ![[42, 31, 12, 11, 26, 4], [37, 7, 24, 24, 36, 8], [8, 32, 7, 9, 43, 34], [27, 5, 29, 46, 27, 4], [32, 26, 12]], ![[41, 18, 31, 30, 40, 14], [11, 45, 22, 6, 38, 25], [40, 13, 32, 19, 29, 18], [35, 13, 35, 45, 9, 32], [26, 36, 7]], ![[2, 33, 15, 5, 14, 17], [36, 39, 10, 9, 34, 6], [17, 3, 13, 46, 6, 6], [24, 6, 40, 32, 10, 28], [33, 43, 36]]]
 h' := ![![[32, 17, 37, 24], [32, 18, 24, 13], [15, 27, 20, 20], [43, 17, 45, 15], [0, 0, 1], [0, 1]], ![[44, 17, 35, 17], [3, 14, 0, 14], [14, 42, 4, 43], [15, 27, 30, 16], [10, 6, 10, 33], [32, 17, 37, 24]], ![[21, 12, 22, 6], [11, 36, 34, 38], [13, 37, 0, 30], [45, 12, 14, 15], [37, 35, 7, 20], [44, 17, 35, 17]], ![[0, 1], [20, 26, 36, 29], [46, 35, 23, 1], [17, 38, 5, 1], [21, 6, 29, 41], [21, 12, 22, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 35, 11], []]
 b := ![[], [], [38, 36, 30, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [17, 20, 41, 44, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5946657, 64730720, -60355872, 38104144, 235997142]
  a := ![16, -8, 23, -11, -73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-150509949, -13686398, -36432678, -129740884, 235997142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5557, 7549, -36389, 8168, 97722]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-5557, 7549, -36389, 8168, 97722]] 
 ![![47, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-5557, 7549, -36389, 8168, 97722], ![146142, 51619, 80179, -35655, -209722], ![12624, -103443, 385138, -80358, -1036212], ![-554064, -183294, -347471, 144064, 912184], ![53022, -11151, 133820, -34335, -358009]]]
  hmulB := by decide  
  f := ![![![-4103, -556, 6583, -2453, -26098]], ![![-4131, -914, 5194, -2085, -20938]], ![![426, -1428, 7240, -2817, -27180]], ![![-5895, -2295, 5004, -2438, -20960]], ![![-1182, -561, 5330, -1971, -20443]]]
  g := ![![![-51266, 7549, -36389, 8168, 97722], ![67998, 51619, 80179, -35655, -209722], ![558105, -103443, 385138, -80358, -1036212], ![-321300, -183294, -347471, 144064, 912184], ![177588, -11151, 133820, -34335, -358009]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-4103, -556, 6583, -2453, -26098]] ![![-5557, 7549, -36389, 8168, 97722]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25673, -5908, 66969, -23589, -243468]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![25673, -5908, 66969, -23589, -243468]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![28, 2, 40, 30, 1]] where
  M :=![![![25673, -5908, 66969, -23589, -243468], ![-305802, -139450, -99409, -11394, 256914], ![975834, -385560, 938930, -400773, -3246534], ![-841896, -609859, 231903, -263389, -1214860], ![458826, -82161, 341736, -127683, -1141069]]]
  hmulB := by decide  
  f := ![![![256417, -36859, 587335, -153822, -1570308]], ![![-1942128, -820337, -594589, 377607, 1519368]], ![![-2238822, 701121, -6457622, 1614696, 17289462]], ![![7601286, 3021350, 2990905, -1613534, -7733362]], ![![2651000, 2187335, -2930400, 249153, 7999061]]]
  g := ![![![129109, 9076, 185013, 137367, -243468], ![-141498, -12326, -195773, -145638, 256914], ![1733562, 115236, 2467930, 1830099, -3246534], ![625928, 34337, 921251, 682687, -1214860], ![611486, 41509, 867632, 643479, -1141069]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [9, 6, 11, 45, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 41, 4, 34], [16, 51, 13, 44], [2, 13, 36, 28], [0, 1]]
 g := ![![[7, 8, 1, 47], [17, 28, 1], [3, 11, 49, 38], [0, 8, 1], []], ![[16, 14, 0, 2, 41, 48], [15, 52, 16], [14, 38, 10, 25, 45, 14], [41, 38, 29], [39, 45, 43, 25, 22, 31]], ![[41, 36, 6, 47, 50, 52], [25, 13, 46], [5, 52, 11, 42, 1, 43], [29, 47, 37], [38, 7, 7, 30, 30, 13]], ![[2, 14, 7, 46, 51, 24], [22, 2, 43], [48, 23, 31, 20, 30, 29], [8, 17, 29], [48, 18, 18, 33, 5, 10]]]
 h' := ![![[43, 41, 4, 34], [46, 28, 32, 43], [26, 42, 43, 52], [0, 34, 49, 12], [0, 0, 0, 1], [0, 1]], ![[16, 51, 13, 44], [39, 16, 22, 32], [42, 51, 36, 49], [42, 49, 49, 49], [27, 1, 34, 33], [43, 41, 4, 34]], ![[2, 13, 36, 28], [0, 16, 32, 35], [15, 43, 18, 24], [32, 12, 42, 31], [44, 28, 7, 39], [16, 51, 13, 44]], ![[0, 1], [3, 46, 20, 49], [25, 23, 9, 34], [34, 11, 19, 14], [0, 24, 12, 33], [2, 13, 36, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [47, 2, 36], []]
 b := ![[], [], [20, 38, 27, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [9, 6, 11, 45, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34431996, 154283039, -128704897, 86612496, 514626230]
  a := ![-21, 9, -23, 8, 96]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-271228348, -16508857, -390825549, -289663668, 514626230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![256417, -36859, 587335, -153822, -1570308]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![256417, -36859, 587335, -153822, -1570308]] 
 ![![53, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![256417, -36859, 587335, -153822, -1570308], ![-1942128, -820337, -594589, 377607, 1519368], ![-2238822, 701121, -6457622, 1614696, 17289462], ![7601286, 3021350, 2990905, -1613534, -7733362], ![-1278120, -83859, -1989672, 575091, 5302501]]]
  hmulB := by decide  
  f := ![![![25673, -5908, 66969, -23589, -243468]], ![![13606, -7090, 48667, -18018, -178902]], ![![39241, -12068, 72049, -26700, -258786]], ![![5913, -16523, 61236, -24998, -229640]], ![![20767, -4337, 38037, -13536, -136373]]]
  g := ![![![427454, -36859, 587335, -153822, -1570308], ![27588, -820337, -594589, 377607, 1519368], ![-4858562, 701121, -6457622, 1614696, 17289462], ![454367, 3021350, 2990905, -1613534, -7733362], ![-1336028, -83859, -1989672, 575091, 5302501]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![25673, -5908, 66969, -23589, -243468]] ![![256417, -36859, 587335, -153822, -1570308]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11805671, 148619507, -139889730, 88099751, 545526772]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![11805671, 148619507, -139889730, 88099751, 545526772]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![4, 30, 1, 0, 0], ![19, 16, 0, 1, 0], ![45, 40, 0, 0, 1]] where
  M :=![![![11805671, 148619507, -139889730, 88099751, 545526772], ![50784798, 628503928, -593493454, 373228569, 2314438634], ![225201660, 2663384781, -2505351533, 1578576759, 9774794952], ![303334398, 3758412991, -3544600952, 2230378744, 13823379890], ![55253244, 637527822, -598759966, 377572746, 2336684075]]]
  hmulB := by decide  
  f := ![![![-18572953643, -4950992427, -15830246128, 5683815343, 41836499796]], ![![23200823214, 21213753758, -32904507300, 3663599703, 89544359962]], ![![13973240120, 11278892613, -14568246811, 1133934371, 39799876848]], ![![-1571360413, 2703695058, -12284385238, 2717226351, 33002226710]], ![![2648113551, 10957127743, -33674955634, 6531406149, 90759150367]]]
  g := ![![![-434766702, -320090771, -139889730, 88099751, 545526772], ![-1844344453, -1357896524, -593493454, 373228569, 2314438634], ![-7790035991, -5736018567, -2505351533, 1578576759, 9774794952], ![-11016060220, -8110590067, -3544600952, 2230378744, 13823379890], ![-1862277499, -1371325426, -598759966, 377572746, 2336684075]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [50, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 58], [0, 1]]
 g := ![![[24, 26], [39, 26], [16], [58, 16], [39, 1]], ![[35, 33], [50, 33], [16], [33, 43], [19, 58]]]
 h' := ![![[39, 58], [56, 47], [48, 47], [50, 55], [56, 55], [0, 1]], ![[0, 1], [1, 12], [52, 12], [12, 4], [18, 4], [39, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [53, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [50, 20, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-380, 12425, -18883, 8098, 62161]
  a := ![-70, 28, -105, 35, 319]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48745, -34527, -18883, 8098, 62161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16985, -1821, 6923, -2466, -20618]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![16985, -1821, 6923, -2466, -20618]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![42, 1, 1, 0, 0], ![45, 53, 0, 1, 0], ![47, 24, 0, 0, 1]] where
  M :=![![![16985, -1821, 6923, -2466, -20618], ![-17466, -277, 2907, -1425, -16650], ![-24300, -27441, -11752, -4104, 33000], ![57624, -17676, 60789, -24064, -211176], ![-11550, -8823, -9288, 453, 30053]]]
  hmulB := by decide  
  f := ![![![518467, 275808, -40405, -60117, 130438]], ![![1473420, 97648, 2290281, -662268, -6103536]], ![![285750, 144392, 4433, -38589, 12]], ![![1637043, 297985, 1880415, -600100, -4993392]], ![![990847, 245151, 911051, -316818, -2411007]]]
  g := ![![![13665, 10454, 6923, -2466, -20618], ![11985, 7999, 2907, -1425, -16650], ![-15204, -10003, -11752, -4104, 33000], ![144282, 106189, 60789, -24064, -211176], ![-17870, -12624, -9288, 453, 30053]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [21, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 58], [0, 1]]
 g := ![![[0, 45], [], [4], [0, 28], [0, 1]], ![[0, 14], [], [4], [0, 31], [0, 58]]]
 h' := ![![[0, 58], [0, 35], [34], [0, 2], [0, 38], [0, 1]], ![[0, 1], [0, 24], [34], [0, 57], [0, 21], [0, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [0, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [21, 0, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-905, 3583, -4838, 2733, 17414]
  a := ![-28, 12, -41, 17, 128]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12528, -9396, -4838, 2733, 17414]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29209, -536242, 518881, -322345, -2016992]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-29209, -536242, 518881, -322345, -2016992]] 
 ![![59, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-29209, -536242, 518881, -322345, -2016992], ![-248766, -2285624, 2116097, -1344462, -8279362], ![-637770, -9660000, 9176764, -5751867, -35731626], ![-1220424, -13633613, 12815177, -8078837, -50022820], ![-117924, -2311497, 2212070, -1381047, -8599489]]]
  hmulB := by decide  
  f := ![![![-173743403, -51723939, -129126459, 49296106, 340328172]], ![![-80189164, -21643067, -67411443, 24348755, 178110440]], ![![-91057320, -27877149, -64978154, 25284810, 171106038]], ![![-74158347, -30419185, -25874646, 15066448, 66551070]], ![![-99156043, -28976472, -75594811, 28522073, 199346105]]]
  g := ![![![1264246, -536242, 518881, -322345, -2016992], ![5244792, -2285624, 2116097, -1344462, -8279362], ![22496229, -9660000, 9176764, -5751867, -35731626], ![31572597, -13633613, 12815177, -8078837, -50022820], ![5404748, -2311497, 2212070, -1381047, -8599489]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![11805671, 148619507, -139889730, 88099751, 545526772]] ![![16985, -1821, 6923, -2466, -20618]]
  ![![-220122713303, -2594385557432, 2446394779345, -1539696910589, -9544122144488]] where
 M := ![![![-220122713303, -2594385557432, 2446394779345, -1539696910589, -9544122144488]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-220122713303, -2594385557432, 2446394779345, -1539696910589, -9544122144488]] ![![-29209, -536242, 518881, -322345, -2016992]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![2096151405665408237, 25468496891757891487, -23997956155354196680, 15107512476379833933, 93604734454524305602]]]
 hmul := by decide  
 g := ![![![![35527989926532343, 431669438843354093, -406745019582274520, 256059533497963287, 1586520922958039078]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18237331, -8949925, -1213751, 2653044, 2504890]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-18237331, -8949925, -1213751, 2653044, 2504890]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![14, 10, 1, 0, 0], ![55, 12, 0, 1, 0], ![3, 34, 0, 0, 1]] where
  M :=![![![-18237331, -8949925, -1213751, 2653044, 2504890], ![-40240122, 333977, -73067443, 20236143, 195005598], ![220766220, 101412879, 38974910, -37077042, -95686656], ![126775596, -12924358, 271811015, -72256216, -726379180], ![47495010, 28195275, -13969464, -3409089, 39589325]]]
  hmulB := by decide  
  f := ![![![-247651, -1023140, 890815, -585765, -3539086]], ![![-73488, -4348006, 4175257, -2599440, -16180956]], ![![-97622, -1247108, 1172426, -738759, -4571840]], ![![-275623, -2203189, 2021398, -1290556, -7923540]], ![![-60813, -2545219, 2438947, -1520298, -9458455]]]
  g := ![![![-2535687, -1865823, -1213751, 2653044, 2504890], ![-11726239, -100688781, -73067443, 20236143, 195005598], ![32810078, 55900567, 38974910, -37077042, -95686656], ![40568046, 374310364, 271811015, -72256216, -726379180], ![5111466, -18643247, -13969464, -3409089, 39589325]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [56, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 60], [0, 1]]
 g := ![![[34, 12], [14], [48, 4], [56, 20], [48, 1]], ![[0, 49], [14], [57, 57], [40, 41], [35, 60]]]
 h' := ![![[48, 60], [25, 16], [57, 21], [36, 59], [57, 52], [0, 1]], ![[0, 1], [0, 45], [28, 40], [1, 2], [52, 9], [48, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [8, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [56, 13, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43240, 6952, -80765, 22607, 224948]
  a := ![-85, 36, -148, 47, 388]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13619, -116474, -80765, 22607, 224948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3191, 510, -7489, 1951, 20026]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-3191, 510, -7489, 1951, 20026]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![9, 53, 1, 0, 0], ![24, 2, 0, 1, 0], ![17, 55, 0, 0, 1]] where
  M :=![![![-3191, 510, -7489, 1951, 20026], ![24960, 10466, 7911, -4908, -20252], ![27588, -9396, 82226, -20439, -220188], ![-97554, -38495, -39369, 20909, 101898], ![16098, 945, 25450, -7323, -67835]]]
  hmulB := by decide  
  f := ![![![1897, -809, 1821, -794, -6302]], ![![-4614, -3661, 1723, -1683, -8390]], ![![-3645, -3569, 2038, -1743, -9244]], ![![552, -792, 1131, -586, -4152]], ![![-3589, -3593, 2132, -1780, -9581]]]
  g := ![![![-5296, -11605, -7489, 1951, 20026], ![6817, 11719, 7911, -4908, -20252], ![57726, 127604, 82226, -20439, -220188], ![-32415, -58986, -39369, 20909, 101898], ![18295, 39306, 25450, -7323, -67835]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [20, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 60], [0, 1]]
 g := ![![[10, 58], [34], [8, 48], [31, 15], [44, 1]], ![[0, 3], [34], [46, 13], [20, 46], [27, 60]]]
 h' := ![![[44, 60], [32, 27], [23, 41], [51, 32], [35, 25], [0, 1]], ![[0, 1], [0, 34], [58, 20], [56, 29], [37, 36], [44, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [58, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [20, 17, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1850, 444, -3500, 990, 9762]
  a := ![-16, 8, -28, 9, 73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2624, -5786, -3500, 990, 9762]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19370321, 268275934, -254677726, 159715406, 992208284]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![19370321, 268275934, -254677726, 159715406, 992208284]] 
 ![![61, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![19370321, 268275934, -254677726, 159715406, 992208284], ![101747544, 1137378163, -1067415176, 673405476, 4166788736], ![379067640, 4815585876, -4544203481, 2858403756, 17718150408], ![567727872, 6795964644, -6402288104, 4031007787, 24975251440], ![86942958, 1152551694, -1089032746, 684525318, 4244760995]]]
  hmulB := by decide  
  f := ![![![-417171102523, -191328357194, -74723613278, 70282243334, 183707160044]], ![![-415197605717, -183828991371, -97483944762, 74672486998, 245057409108]], ![![-308197747671, -143624423094, -47230742159, 50293929186, 114255397044]], ![![-225004617386, -127868031760, 46181524868, 20236415783, -133720192264]], ![![-275437217575, -124719725888, -54961394772, 47553203672, 136434743767]]]
  g := ![![![-820105263, 268275934, -254677726, 159715406, 992208284], ![-3457741357, 1137378163, -1067415176, 673405476, 4166788736], ![-14675749359, 4815585876, -4544203481, 2858403756, 17718150408], ![-20697997902, 6795964644, -6402288104, 4031007787, 24975251440], ![-3514351235, 1152551694, -1089032746, 684525318, 4244760995]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-18237331, -8949925, -1213751, 2653044, 2504890]] ![![-3191, 510, -7489, 1951, 20026]]
  ![![-417171102523, -191328357194, -74723613278, 70282243334, 183707160044]] where
 M := ![![![-417171102523, -191328357194, -74723613278, 70282243334, 183707160044]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-417171102523, -191328357194, -74723613278, 70282243334, 183707160044]] ![![19370321, 268275934, -254677726, 159715406, 992208284]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB314I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB314I1 : PrimesBelowBoundCertificateInterval O 23 61 314 where
  m := 9
  g := ![1, 3, 2, 3, 2, 2, 2, 3, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB314I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact ![29791, 31, 31]
    · exact ![1874161, 37]
    · exact ![1681, 1681, 41]
    · exact ![79507, 1849]
    · exact ![4879681, 47]
    · exact ![7890481, 53]
    · exact ![3481, 3481, 59]
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
      exact NI31N1
      exact NI31N2
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
  β := ![I31N1, I31N2, I37N1, I41N2, I47N1, I53N1, I59N2, I61N2]
  Il := ![[], [I31N1, I31N2], [I37N1], [I41N2], [], [I47N1], [I53N1], [I59N2], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
