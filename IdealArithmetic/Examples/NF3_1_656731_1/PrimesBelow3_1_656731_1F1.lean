
import IdealArithmetic.Examples.NF3_1_656731_1.RI3_1_656731_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![16, 8, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![16, 8, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![16, 8, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![16, 8, 1], ![95, -8, 73], ![703, -185, 0]]]
  hmulB := by decide  
  f := ![![![-15, -8, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -8, 37]], ![![0, 0, 1], ![-29, -16, 73], ![19, -5, 0]]]
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
  c := ![2129, 121, -2043]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![941, 445, -2043]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![1, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![1, 1, 0]] 
 ![![37, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![1, 1, 0], ![1, 1, 9], ![87, -24, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![37, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, -8], ![4, 33, 0]]]
  g := ![![![1, 0, 0], ![-1, 37, 0], ![0, 0, 37]], ![![0, 1, 0], ![0, 1, 9], ![3, -24, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![16, 8, 1]] ![![37, 0, 0], ![1, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![37, 37, 0]], ![![592, 296, 37], ![111, 0, 74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![1, 1, 0]]], ![![![16, 8, 1]], ![![3, 0, 2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191213150497795020, -2123302903294684, -7657972995691961]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-191213150497795020, -2123302903294684, -7657972995691961]] 
 ![![41, 0, 0], ![0, 41, 0], ![8, 4, 1]] where
  M :=![![![-191213150497795020, -2123302903294684, -7657972995691961], ![-668366953528495291, -7421798601187956, -26767699125344117], ![-238333163556481235, -2646541290771311, -9545101504482640]]]
  hmulB := by decide  
  f := ![![![-96411133, 25125729, 6888968]], ![![624465945, -261746365, 233020529]], ![![96603315, -34165228, 18306664]]]
  g := ![![![-3169496744689252, 695331440962760, -7657972995691961], ![-11078667329896155, 2430463363419232, -26767699125344117], ![-3950545159039515, 866679627491689, -9545101504482640]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [13, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 40], [0, 1]]
 g := ![![[31, 4], [18], [9], [38, 8], [1]], ![[18, 37], [18], [9], [12, 33], [1]]]
 h' := ![![[7, 40], [30, 39], [10, 10], [39, 3], [28, 7], [0, 1]], ![[0, 1], [16, 2], [39, 31], [19, 38], [36, 34], [7, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [25, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [13, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3996, 4275, -7982]
  a := ![2, -2, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1460, 883, -7982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![96411133, -25125729, -6888968]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![96411133, -25125729, -6888968]] 
 ![![41, 0, 0], ![4, 1, 0], ![12, 0, 1]] where
  M :=![![![96411133, -25125729, -6888968], ![-624465945, 261746365, -233020529], ![-2234161199, 554794720, 236620636]]]
  hmulB := by decide  
  f := ![![![191213150497795020, 2123302903294684, 7657972995691961]], ![![34956574524870131, 388170980838212, 1399990027027121]], ![![61777828525122475, 686004295861159, 2474165303726492]]]
  g := ![![![6819065, -25125729, -6888968], ![27434023, 261746365, -233020529], ![-177872871, 554794720, 236620636]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-191213150497795020, -2123302903294684, -7657972995691961]] ![![96411133, -25125729, -6888968]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85710056647479666564380507, 951756778481844064611778, 3432636811625549956023424]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![85710056647479666564380507, 951756778481844064611778, 3432636811625549956023424]] 
 ![![43, 0, 0], ![0, 43, 0], ![13, 34, 1]] where
  M :=![![![85710056647479666564380507, 951756778481844064611778, 3432636811625549956023424], ![299591159389904690238649666, 3326773168466467619818331, 11998447817962146537529426], ![106831297409299283313388654, 1186294997814592141481296, 4278529946948311684430109]]]
  hmulB := by decide  
  f := ![![![-2083627490419, 552204061714, 123113502188]], ![![11263078752070, -5038351542931, 5092950057614]], ![![9413048094869, -4105032619144, 3959875116421]]]
  g := ![![![955483211542965514792465, -2692044065506671033492666, 3432636811625549956023424], ![3339798552474343843041096, -9409777968424337550143771, 11998447817962146537529426], ![1190939723231889102692959, -3355435423219255933235870, 4278529946948311684430109]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 42], [0, 1]]
 g := ![![[7, 23], [13, 40], [36], [40, 25], [1]], ![[36, 20], [41, 3], [36], [36, 18], [1]]]
 h' := ![![[5, 42], [40, 18], [11, 13], [4, 6], [13, 5], [0, 1]], ![[0, 1], [1, 25], [33, 30], [34, 37], [38, 38], [5, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [9, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1811219, 1925003, -6467685]
  a := ![-65, 1, -521]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1997468, 5158751, -6467685]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2083627490419, 552204061714, 123113502188]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-2083627490419, 552204061714, 123113502188]] 
 ![![43, 0, 0], ![37, 1, 0], ![20, 0, 1]] where
  M :=![![![-2083627490419, 552204061714, 123113502188], ![11263078752070, -5038351542931, 5092950057614], ![48903547884434, -12391102965820, -4486147481217]]]
  hmulB := by decide  
  f := ![![![85710056647479666564380507, 951756778481844064611778, 3432636811625549956023424]], ![![80717750124340752398156475, 896320324937086000243119, 3232697903444360346753398]], ![![42349591403695177083744158, 470265827150034265900392, 1696075957661844437323223]]]
  g := ![![![-580870879479, 552204061714, 123113502188], ![2228443829959, -5038351542931, 5092950057614], ![13885983889398, -12391102965820, -4486147481217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![85710056647479666564380507, 951756778481844064611778, 3432636811625549956023424]] ![![-2083627490419, 552204061714, 123113502188]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![7, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![7, 1, 0]] 
 ![![47, 0, 0], ![7, 1, 0], ![26, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![7, 1, 0], ![1, 7, 9], ![87, -24, 8]]]
  hmulB := by decide  
  f := ![![![-1037, -7554, -9720], ![-282, 50760, 0]], ![![-153, -1119, -1440], ![-46, 7520, 0]], ![![-575, -4179, -5377], ![-147, 28080, 0]]]
  g := ![![![1, 0, 0], ![-7, 47, 0], ![-26, 0, 47]], ![![0, 1, 0], ![-6, 7, 9], ![1, -24, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -6, 8]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![11, -6, 8]] 
 ![![47, 0, 0], ![32, 1, 0], ![43, 0, 1]] where
  M :=![![![11, -6, 8], ![690, -181, -46], ![-466, 200, -187]]]
  hmulB := by decide  
  f := ![![![-43047, -478, -1724]], ![![-32510, -361, -1302]], ![![-40525, -450, -1623]]]
  g := ![![![-3, -6, 8], ![180, -181, -46], ![25, 200, -187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![7, 1, 0]] ![![47, 0, 0], ![7, 1, 0]]
  ![![43047, 478, 1724]] where
 M := ![![![2209, 0, 0], ![329, 47, 0]], ![![329, 47, 0], ![50, 14, 9]]]
 hmul := by decide  
 g := ![![![![-517, 282, -376]], ![![-767, 223, -10]]], ![![![-767, 223, -10]], ![![-128, 22, 41]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![43047, 478, 1724]] ![![11, -6, 8]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11885, 132, 476]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![11885, 132, 476]] 
 ![![53, 0, 0], ![0, 53, 0], ![40, 27, 1]] where
  M :=![![![11885, 132, 476], ![41544, 461, 1664], ![14816, 164, 593]]]
  hmulB := by decide  
  f := ![![![9, -4, 4]], ![![344, -87, -32]], ![![176, -45, -15]]]
  g := ![![![-135, -240, 476], ![-472, -839, 1664], ![-168, -299, 593]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [32, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 52], [0, 1]]
 g := ![![[10, 46], [9], [5, 15], [42], [51, 1]], ![[24, 7], [9], [28, 38], [42], [49, 52]]]
 h' := ![![[51, 52], [31, 29], [52, 3], [49, 42], [11, 25], [0, 1]], ![[0, 1], [26, 24], [46, 50], [18, 11], [14, 28], [51, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [6, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [32, 2, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-746, 3437, -8655]
  a := ![-2, 1, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6518, 4474, -8655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -4, 4]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![9, -4, 4]] 
 ![![53, 0, 0], ![21, 1, 0], ![10, 0, 1]] where
  M :=![![![9, -4, 4], ![344, -87, -32], ![-320, 124, -91]]]
  hmulB := by decide  
  f := ![![![11885, 132, 476]], ![![5493, 61, 220]], ![![2522, 28, 101]]]
  g := ![![![1, -4, 4], ![47, -87, -32], ![-38, 124, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![11885, 132, 476]] ![![9, -4, 4]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [58, 29, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 46], [14, 58, 13], [0, 1]]
 g := ![![[1, 20, 21], [3, 12, 46], [0, 16], [2, 27, 48], [1]], ![[58, 22, 18, 22], [2, 14, 31, 25], [17, 21], [7, 3, 24, 53], [15, 5, 26, 45]], ![[16, 47], [45, 13, 44, 30], [56, 57], [5, 25, 11, 33], [20, 34, 57, 14]]]
 h' := ![![[1, 0, 46], [3, 0, 32], [4, 14, 39], [2, 29, 4], [1, 30, 15], [0, 1]], ![[14, 58, 13], [30, 7, 27], [38, 3, 15], [27, 23, 32], [16, 42, 8], [1, 0, 46]], ![[0, 1], [10, 52], [26, 42, 5], [18, 7, 23], [50, 46, 36], [14, 58, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 38], []]
 b := ![[], [41, 40, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [58, 29, 44, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![269276, 107380, -511884]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4564, 1820, -8676]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [56, 59, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 52, 54], [58, 8, 7], [0, 1]]
 g := ![![[1, 26, 27], [11, 1], [31, 21, 45], [3, 16, 4], [1]], ![[48, 25, 42, 40], [43, 49], [14, 11, 22, 44], [56, 7, 11, 33], [9, 3, 4, 23]], ![[58, 43, 5, 31], [50, 3], [26, 60, 18, 30], [47, 41, 14, 51], [14, 6, 32, 38]]]
 h' := ![![[5, 52, 54], [46, 35, 24], [33, 26, 60], [15, 50, 17], [5, 2, 2], [0, 1]], ![[58, 8, 7], [7, 5, 8], [55, 17, 54], [27, 41, 30], [48, 29, 2], [5, 52, 54]], ![[0, 1], [42, 21, 29], [55, 18, 8], [56, 31, 14], [43, 30, 57], [58, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 5], []]
 b := ![[], [41, 35, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [56, 59, 59, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21774682, 6767767, -547963]
  a := ![2, 19, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-356962, 110947, -8983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![538974318, 5984974, 21585601]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![538974318, 5984974, 21585601]] 
 ![![67, 0, 0], ![0, 67, 0], ![59, 40, 1]] where
  M :=![![![538974318, 5984974, 21585601], ![1883932261, 20919894, 75450367], ![671791945, 7459831, 26904868]]]
  hmulB := by decide  
  f := ![![![-955, 597, -908]], ![![-78399, 20837, 4465]], ![![-46966, 12657, 2186]]]
  g := ![![![-10963823, -12797598, 21585601], ![-38322976, -44732758, 75450367], ![-13665601, -15951267, 26904868]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [34, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 66], [0, 1]]
 g := ![![[63, 4], [61, 24], [55], [36], [4], [1]], ![[4, 63], [42, 43], [55], [36], [4], [1]]]
 h' := ![![[2, 66], [3, 65], [42, 52], [6, 51], [15, 6], [33, 2], [0, 1]], ![[0, 1], [66, 2], [12, 15], [41, 16], [27, 61], [37, 65], [2, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [1, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [34, 65, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6934, 4654, -7994]
  a := ![-2, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6936, 4842, -7994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-955, 597, -908]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-955, 597, -908]] 
 ![![67, 0, 0], ![41, 1, 0], ![59, 0, 1]] where
  M :=![![![-955, 597, -908], ![-78399, 20837, 4465], ![45583, -20684, 21434]]]
  hmulB := by decide  
  f := ![![![538974318, 5984974, 21585601]], ![![357938497, 3974684, 14335224]], ![![484645921, 5381691, 19409781]]]
  g := ![![![420, 597, -908], ![-17853, 20837, 4465], ![-5537, -20684, 21434]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![538974318, 5984974, 21585601]] ![![-955, 597, -908]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [52, 8, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 60, 16], [63, 10, 55], [0, 1]]
 g := ![![[45, 16, 32], [16, 25, 37], [43, 8, 24], [64, 5], [66, 1], []], ![[4, 44, 48, 4], [35, 18, 22, 12], [53, 67, 40, 36], [32, 58], [18, 29], [1, 43]], ![[0, 15, 29, 65], [40, 40, 63, 39], [32, 35, 5, 28], [23, 25], [50, 50], [33, 43]]]
 h' := ![![[3, 60, 16], [20, 10, 23], [36, 26, 45], [17, 17, 33], [47, 59, 17], [0, 0, 1], [0, 1]], ![[63, 10, 55], [55, 10, 35], [25, 63, 14], [69, 50, 34], [61, 54, 49], [28, 33, 10], [3, 60, 16]], ![[0, 1], [0, 51, 13], [38, 53, 12], [35, 4, 4], [33, 29, 5], [52, 38, 60], [63, 10, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 8], []]
 b := ![[], [5, 55, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [52, 8, 5, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![612872, -1374205, 3382866]
  a := ![2, 1, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8632, -19355, 47646]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![11, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![11, 1, 0]] 
 ![![73, 0, 0], ![11, 1, 0], ![11, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![11, 1, 0], ![1, 11, 9], ![87, -24, 12]]]
  hmulB := by decide  
  f := ![![![-1244, -14295, -11700], ![-365, 94900, 0]], ![![-195, -2145, -1755], ![1, 14235, 0]], ![![-198, -2155, -1763], ![15, 14300, 0]]]
  g := ![![![1, 0, 0], ![-11, 73, 0], ![-11, 0, 73]], ![![0, 1, 0], ![-3, 11, 9], ![3, -24, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7940010992, 2834192520, -1577816943]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-7940010992, 2834192520, -1577816943]] 
 ![![73, 0, 0], ![22, 1, 0], ![68, 0, 1]] where
  M :=![![![-7940010992, 2834192520, -1577816943], ![-134435881521, 29927595640, 23929915737], ![235530030639, -79065339081, 32761788160]]]
  hmulB := by decide  
  f := ![![![2872508450421482640097, 31897416661145286183, 115042255650080615760]], ![![1003229583116312012869, 11140239470749919971, 40178748354824133399]], ![![2724807474900424982669, 30257289351245984964, 109126919392961301640]]]
  g := ![![![506839804, 2834192520, -1577816943], ![-33151743229, 29927595640, 23929915737], ![-3463480883, -79065339081, 32761788160]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-34, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-34, 1, 0]] 
 ![![73, 0, 0], ![39, 1, 0], ![42, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-34, 1, 0], ![1, -34, 9], ![87, -24, -33]]]
  hmulB := by decide  
  f := ![![![-10, 1529, -405], ![73, 3285, 0]], ![![11, 815, -216], ![74, 1752, 0]], ![![-16, 880, -233], ![20, 1890, 0]]]
  g := ![![![1, 0, 0], ![-39, 73, 0], ![-42, 0, 73]], ![![-1, 1, 0], ![13, -34, 9], ![33, -24, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![11, 1, 0]] ![![-7940010992, 2834192520, -1577816943]]
  ![![73, 0, 0], ![27, 28, 1]] where
 M := ![![![-579620802416, 206896053960, -115180636839]], ![![-221776002433, 61103713360, 6573929364]]]
 hmul := by decide  
 g := ![![![![-7401034022, 3393131600, -1557854833], ![-1457234030, 0, 0]]], ![![![-2807209018, 1076404412, 98602657], ![-624064597, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![27, 28, 1]] ![![73, 0, 0], ![-34, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2482, 73, 0]], ![![1971, 2044, 73], ![-803, -949, 219]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-34, 1, 0]]], ![![![27, 28, 1]], ![![-11, -13, 3]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133460, -1482, -5345]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-133460, -1482, -5345]] 
 ![![79, 0, 0], ![0, 79, 0], ![75, 68, 1]] where
  M :=![![![-133460, -1482, -5345], ![-466497, -5180, -18683], ![-166349, -1847, -6662]]]
  hmulB := by decide  
  f := ![![![-21, 11, -14]], ![![-1207, 315, 85]], ![![-1048, 277, 64]]]
  g := ![![![3385, 4582, -5345], ![11832, 16016, -18683], ![4219, 5711, -6662]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [75, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 78], [0, 1]]
 g := ![![[48, 4], [45, 45], [50, 9], [37, 9], [50], [1]], ![[26, 75], [74, 34], [40, 70], [27, 70], [50], [1]]]
 h' := ![![[34, 78], [22, 77], [42, 19], [69, 76], [58, 76], [4, 34], [0, 1]], ![[0, 1], [33, 2], [56, 60], [46, 3], [35, 3], [54, 45], [34, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [46, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [75, 45, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11075, 11200, -39800]
  a := ![-5, 0, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37925, 34400, -39800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -11, 14]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![21, -11, 14]] 
 ![![79, 0, 0], ![19, 1, 0], ![39, 0, 1]] where
  M :=![![![21, -11, 14], ![1207, -315, -85], ![-859, 362, -326]]]
  hmulB := by decide  
  f := ![![![133460, 1482, 5345]], ![![38003, 422, 1522]], ![![67991, 755, 2723]]]
  g := ![![![-4, -11, 14], ![133, -315, -85], ![63, 362, -326]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-133460, -1482, -5345]] ![![21, -11, 14]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB230I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB230I1 : PrimesBelowBoundCertificateInterval O 31 79 230 where
  m := 11
  g := ![2, 2, 2, 3, 2, 1, 1, 2, 1, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB230I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1]
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
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I43N1, I47N0, I47N1, I53N1, I67N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N0, I47N0, I47N1], [I53N1], [], [], [I67N1], [], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
