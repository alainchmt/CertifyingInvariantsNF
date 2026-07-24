
import IdealArithmetic.Examples.NF3_1_89544_1.RI3_1_89544_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [5, 17, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 27, 16], [12, 9, 21], [0, 1]]
 g := ![![[1, 26, 7], [0, 27], [9, 9, 25], [7, 1], []], ![[9, 23, 18, 33], [28, 36], [29, 17, 15, 21], [16, 7], [29, 34]], ![[8, 11, 1, 27], [3, 4], [17, 3, 16, 21], [22, 26], [24, 34]]]
 h' := ![![[32, 27, 16], [27, 9, 9], [29, 28, 29], [2, 24, 32], [0, 0, 1], [0, 1]], ![[12, 9, 21], [12, 23, 3], [35, 6, 6], [1, 22, 6], [28, 29, 9], [32, 27, 16]], ![[0, 1], [18, 5, 25], [25, 3, 2], [22, 28, 36], [24, 8, 27], [12, 9, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 32], []]
 b := ![[], [34, 35, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [5, 17, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5143, 481, 481]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-139, 13, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀


def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![600359513, -252598336, 43601696]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![600359513, -252598336, 43601696]] 
 ![![41, 0, 0], ![2, 1, 0], ![37, 0, 1]] where
  M :=![![![600359513, -252598336, 43601696], ![-2877711936, 1210783257, -208996640], ![13793778240, -5803664896, 1001786617]]]
  hmulB := by decide  
  f := ![![![322129, 5696, -12832]], ![![36370, 3753, -800]], ![![302189, 23360, -8279]]]
  g := ![![![-12383087, -252598336, 43601696], ![59356030, 1210783257, -208996640], ![-284512117, -5803664896, 1001786617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 32, -16]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![521, 32, -16]] 
 ![![41, 0, 0], ![19, 1, 0], ![8, 0, 1]] where
  M :=![![![521, 32, -16], ![1056, 297, 16], ![-1056, 1280, 313]]]
  hmulB := by decide  
  f := ![![![72481, -30496, 5264]], ![![25115, -10567, 1824]], ![![54760, -23040, 3977]]]
  g := ![![![1, 32, -16], ![-115, 297, 16], ![-680, 1280, 313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![600359513, -252598336, 43601696]] ![![521, 32, -16]]
  ![![72481, -30496, 5264]] where
 M := ![![![72481, -30496, 5264]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![72481, -30496, 5264]] ![![521, 32, -16]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [21, 34, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 6], [18, 36], [0, 1]]
 g := ![![[42, 4, 9], [3, 41, 40], [28, 10], [25, 39, 1], []], ![[10, 13, 23], [14, 6, 21], [23, 17], [38, 13, 36], []], ![[20, 26, 11], [27, 39, 25], [36, 16], [19, 34, 6], []]]
 h' := ![![[21, 6], [23, 21, 3], [9, 27, 30], [34, 8, 15], [0, 0, 1], [0, 1]], ![[18, 36], [24, 22, 22], [3, 25, 5], [23, 1, 24], [11, 37, 36], [21, 6]], ![[0, 1], [40, 0, 18], [24, 34, 8], [7, 34, 4], [23, 6, 6], [18, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31], []]
 b := ![[], [10, 15, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [21, 34, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117734, -51170, 5633]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2738, -1190, 131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5521, -2323, 401]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![5521, -2323, 401]] 
 ![![47, 0, 0], ![0, 47, 0], ![46, 18, 1]] where
  M :=![![![5521, -2323, 401], ![-26466, 11135, -1922], ![126852, -53374, 9213]]]
  hmulB := by decide  
  f := ![![![41, -25, -7]], ![![462, -57, -32]], ![![262, -46, -21]]]
  g := ![![![-275, -203, 401], ![1318, 973, -1922], ![-6318, -4664, 9213]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [9, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[42, 21], [14, 7], [38, 27], [28, 4], [1]], ![[0, 26], [0, 40], [31, 20], [20, 43], [1]]]
 h' := ![![[45, 46], [15, 31], [34, 17], [30, 36], [38, 45], [0, 1]], ![[0, 1], [0, 16], [0, 30], [5, 11], [42, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [3, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [9, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4043, -206, 140]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51, -58, 140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 25, 7]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-41, 25, 7]] 
 ![![47, 0, 0], ![28, 1, 0], ![15, 0, 1]] where
  M :=![![![-41, 25, 7], ![-462, 57, 32], ![-2112, -14, 89]]]
  hmulB := by decide  
  f := ![![![-5521, 2323, -401]], ![![-2726, 1147, -198]], ![![-4461, 1877, -324]]]
  g := ![![![-18, 25, 7], ![-54, 57, 32], ![-65, -14, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![5521, -2323, 401]] ![![-41, 25, 7]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-390012421, -9016725, 15093771]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-390012421, -9016725, 15093771]] 
 ![![53, 0, 0], ![0, 53, 0], ![46, 16, 1]] where
  M :=![![![-390012421, -9016725, 15093771], ![-996188886, -178699627, 6077046], ![-401085036, -911110242, -172622581]]]
  hmulB := by decide  
  f := ![![![-686499050720423, 288841126229619, -49857664059039]], ![![3290605827896574, -1384506347546969, 238983462170580]], ![![99959026602782, -42057272752912, 7259621936549]]]
  g := ![![![-20458979, -4726737, 15093771], ![-24070434, -5206271, 6077046], ![142255730, 34921718, -172622581]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [15, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 52], [0, 1]]
 g := ![![[9, 46], [11], [1, 4], [7], [24, 1]], ![[0, 7], [11], [44, 49], [7], [48, 52]]]
 h' := ![![[24, 52], [7, 24], [38, 8], [16, 2], [11, 31], [0, 1]], ![[0, 1], [0, 29], [18, 45], [11, 51], [13, 22], [24, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [21, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [15, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-153, -521, 37]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -21, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-686499050720423, 288841126229619, -49857664059039]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-686499050720423, 288841126229619, -49857664059039]] 
 ![![53, 0, 0], ![36, 1, 0], ![29, 0, 1]] where
  M :=![![![-686499050720423, 288841126229619, -49857664059039], ![3290605827896574, -1384506347546969, 238983462170580], ![-15772908503258280, 6636374298284694, -1145522885376389]]]
  hmulB := by decide  
  f := ![![![-390012421, -9016725, 15093771]], ![![-283710114, -9496259, 10367034]], ![![-220970665, -22124439, 5001826]]]
  g := ![![![-181866176174992, 288841126229619, -49857664059039], ![871741772389446, -1384506347546969, 238983462170580], ![-4178532444633811, 6636374298284694, -1145522885376389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-390012421, -9016725, 15093771]] ![![-686499050720423, 288841126229619, -49857664059039]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4878994051656154855959453067117, -2052812943104702052628947743993, 354341708292598839929726645299]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![4878994051656154855959453067117, -2052812943104702052628947743993, 354341708292598839929726645299]] 
 ![![59, 0, 0], ![0, 59, 0], ![17, 9, 1]] where
  M :=![![![4878994051656154855959453067117, -2052812943104702052628947743993, 354341708292598839929726645299], ![-23386552747311523435361958589734, 9839777967752538614975626101303, -1698471234812103212699221098694], ![112099101497598812038148592513804, -47165150034680968413151053971450, 8141306732940435402276405002609]]]
  hmulB := by decide  
  f := ![![![-4510055879576047, 127135769599393, 222818941964755]], ![![-14706050169673830, -1390590692069477, 349954711564148]], ![![-3934278177001543, -341706650054430, 99947092152082]]]
  g := ![![![-19403643886746193607557625474, -88845564707425281559262500876, 354341708292598839929726645299], ![93007766855834426788555933696, 425864730187482500496078237111, -1698471234812103212699221098694], ![-445815473938789657636445636111, -2041303570019404864976927101609, 8141306732940435402276405002609]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [35, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 58], [0, 1]]
 g := ![![[23, 27], [8, 53], [25], [50, 49], [21, 1]], ![[0, 32], [0, 6], [25], [17, 10], [42, 58]]]
 h' := ![![[21, 58], [15, 33], [56, 17], [20, 5], [32, 52], [0, 1]], ![[0, 1], [0, 26], [0, 42], [7, 54], [3, 7], [21, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [33, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [35, 38, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-163, -62, -20]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 2, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4510055879576047, 127135769599393, 222818941964755]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-4510055879576047, 127135769599393, 222818941964755]] 
 ![![59, 0, 0], ![49, 1, 0], ![18, 0, 1]] where
  M :=![![![-4510055879576047, 127135769599393, 222818941964755], ![-14706050169673830, -1390590692069477, 349954711564148], ![-23097010963233768, -9806684207775758, -1040635980505329]]]
  hmulB := by decide  
  f := ![![![4878994051656154855959453067117, -2052812943104702052628947743993, 354341708292598839929726645299]], ![![3655663657353221432316122740661, -1538102648209794270573607006006, 265496143585173558370464144423]], ![![3388491430973044058396927927490, -1425691237467213650177493446836, 246092499698427364762906518949]]]
  g := ![![![-250007619412066, 127135769599393, 222818941964755], ![798876422602981, -1390590692069477, 349954711564148], ![8070541743506344, -9806684207775758, -1040635980505329]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![4878994051656154855959453067117, -2052812943104702052628947743993, 354341708292598839929726645299]] ![![-4510055879576047, 127135769599393, 222818941964755]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [58, 28, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 8, 35], [53, 52, 26], [0, 1]]
 g := ![![[40, 56, 16], [17, 60], [53, 18, 20], [6, 48, 39], [1]], ![[59, 34, 24, 40], [25, 47], [2, 4, 19, 11], [33, 52, 2, 37], [33, 34, 17, 53]], ![[31, 33, 56, 43], [40, 4], [33, 11, 43, 2], [52, 58, 29, 55], [28, 11, 29, 8]]]
 h' := ![![[59, 8, 35], [17, 27, 4], [37, 53, 11], [18, 46, 9], [3, 33, 51], [0, 1]], ![[53, 52, 26], [60, 2, 55], [30, 49, 48], [7, 39, 4], [30, 6, 25], [59, 8, 35]], ![[0, 1], [2, 32, 2], [59, 20, 2], [26, 37, 48], [60, 22, 46], [53, 52, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 48], []]
 b := ![[], [40, 56, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [58, 28, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-611525, 53619, 26535]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10025, 879, 435]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16243588346519, 2867462628149, 1305206152143]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-16243588346519, 2867462628149, 1305206152143]] 
 ![![67, 0, 0], ![26, 1, 0], ![61, 0, 1]] where
  M :=![![![-16243588346519, 2867462628149, 1305206152143], ![-86143606041438, 2029297783483, 4172668780292], ![-275396139499272, -27726243117350, 6201966563775]]]
  hmulB := by decide  
  f := ![![![128278066051656569784394525, -53972370435232214821683525, 9316319835599215405185439]], ![![40602277734231680561970428, -17083210262178985073235537, 2948780076506665688333184]], ![![160780020428758637587118503, -67647409165575750935759809, 11676806016745742175474692]]]
  g := ![![![-2543510327748, 2867462628149, 1305206152143], ![-5872211104624, 2029297783483, 4172668780292], ![1002480912859, -27726243117350, 6201966563775]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62739449, -12628180, -5365208]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![62739449, -12628180, -5365208]] 
 ![![67, 0, 0], ![48, 1, 0], ![41, 0, 1]] where
  M :=![![![62739449, -12628180, -5365208], ![354103728, -12373463, -17993388], ![1187563608, 102196296, -30366851]]]
  hmulB := by decide  
  f := ![![![-2214600713365861, 931782445330748, -160837539798536]], ![![-1428142636042656, 600884046348217, -103720253802948]], ![![-2114641686763079, 889725172577836, -153577917861987]]]
  g := ![![![13266651, -12628180, -5365208], ![25160580, -12373463, -17993388], ![-36907727, 102196296, -30366851]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12025200401, -2240818202, -990872298]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![12025200401, -2240818202, -990872298]] 
 ![![67, 0, 0], ![59, 1, 0], ![3, 0, 1]] where
  M :=![![![12025200401, -2240818202, -990872298], ![65397571668, -1847011771, -3231690500], ![213291573000, 20153904668, -5078702271]]]
  hmulB := by decide  
  f := ![![![-74511605129422685941, 31350394323449623806, -5411478097666661242]], ![![-60283987286416997441, 25364193531145848675, -4378183455769403742]], ![![-28888108750596172941, 12154530814586716258, -2098027112895118873]]]
  g := ![![![2197105839, -2240818202, -990872298], ![2747258771, -1847011771, -3231690500], ![-14336607397, 20153904668, -5078702271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-16243588346519, 2867462628149, 1305206152143]] ![![62739449, -12628180, -5365208]]
  ![![1546280751107553523385, 303033749017886957761, -4080138244743979553]] where
 M := ![![![1546280751107553523385, 303033749017886957761, -4080138244743979553]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![1546280751107553523385, 303033749017886957761, -4080138244743979553]] ![![12025200401, -2240818202, -990872298]]
  ![![67, 0, 0]] where
 M := ![![![37541748123218218376496544323733, -4106871671147165511400390711905, -2490756241714022013575217994367]]]
 hmul := by decide  
 g := ![![![![560324598854003259350694691399, -61296592106674112110453592715, -37175466294239134530973402901]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [35, 60, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 29, 58], [55, 41, 13], [0, 1]]
 g := ![![[45, 37, 45], [60], [68, 55, 1], [], [42, 1], []], ![[67, 33, 22, 5], [69, 51, 3, 27], [11, 63, 34, 20], [25, 27], [55, 48], [25, 27]], ![[29, 36, 64, 33], [62, 68, 36, 44], [40, 16, 36, 69], [70, 27], [54, 60], [70, 27]]]
 h' := ![![[58, 29, 58], [30, 41, 51], [34, 42], [15, 42, 1], [21, 1], [0, 0, 1], [0, 1]], ![[55, 41, 13], [56, 62, 67], [56, 11, 22], [41, 7, 63], [8, 29, 58], [4, 67, 41], [58, 29, 58]], ![[0, 1], [15, 39, 24], [1, 18, 49], [60, 22, 7], [5, 41, 13], [7, 4, 29], [55, 41, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 22], []]
 b := ![[], [32, 31, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [35, 60, 29, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2769, 1065, -355]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, 15, -5]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [52, 60, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 46, 58], [53, 26, 15], [0, 1]]
 g := ![![[42, 66, 64], [19, 4], [32, 27], [29, 68, 27], [59, 1], []], ![[32, 68, 23, 15], [13, 64], [2, 48], [59, 54, 10, 21], [20, 19], [69, 6]], ![[65, 4, 44, 52], [20, 27], [66, 1], [70, 65, 50, 7], [19, 72], [39, 6]]]
 h' := ![![[6, 46, 58], [31, 22, 65], [56, 37, 2], [25, 57, 10], [71, 58, 63], [0, 0, 1], [0, 1]], ![[53, 26, 15], [36, 19, 46], [36, 34, 8], [33, 49, 62], [23, 58, 38], [25, 42, 26], [6, 46, 58]], ![[0, 1], [59, 32, 35], [2, 2, 63], [52, 40, 1], [7, 30, 45], [51, 31, 46], [53, 26, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 45], []]
 b := ![[], [26, 26, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [52, 60, 14, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-146, -12702, 1533]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -174, 21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3112390884041742011218645, -1309523279413140610172964, 226040427811406086356270]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![3112390884041742011218645, -1309523279413140610172964, 226040427811406086356270]] 
 ![![79, 0, 0], ![17, 1, 0], ![27, 0, 1]] where
  M :=![![![3112390884041742011218645, -1309523279413140610172964, 226040427811406086356270], ![-14918668235552801699513820, 6276956873401427220206425, -1083482851601734523816694], ![71509868205714478571901804, -30087428157977085032947536, 5193474021799692696389731]]]
  hmulB := by decide  
  f := ![![![-26153312744309, -3178051218036, 475277626266]], ![![-6024995442871, -930712616243, 68062608288]], ![![-6680460595437, -1962209322852, -118603843787]]]
  g := ![![![243939178267812253829617, -1309523279413140610172964, 226040427811406086356270], ![-1169277191014306737974333, 6276956873401427220206425, -1083482851601734523816694], ![5604713269654850902904901, -30087428157977085032947536, 5193474021799692696389731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1732603, -103268889, -21619769]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![1732603, -103268889, -21619769]] 
 ![![79, 0, 0], ![28, 1, 0], ![6, 0, 1]] where
  M :=![![![1732603, -103268889, -21619769], ![1426904754, -300944163, -124888658], ![8242651428, -321536458, -425832821]]]
  hmulB := by decide  
  f := ![![![87995645156080459, -37023738377367667, 6390769674402615]], ![![25849205896957978, -10875927265425033, 1877323825067192]], ![![32275313991546534, -13579680893877080, 2344026201786933]]]
  g := ![![![38265571, -103268889, -21619769], ![134211054, -300944163, -124888658], ![250641382, -321536458, -425832821]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47599, 2911, 2679]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-47599, 2911, 2679]] 
 ![![79, 0, 0], ![33, 1, 0], ![17, 0, 1]] where
  M :=![![![-47599, 2911, 2679], ![-176814, -10093, 5590], ![-368940, -98554, -4503]]]
  hmulB := by decide  
  f := ![![![-596365639, 250917933, -43311637]], ![![-212930355, 89589408, -15464275]], ![![-301775081, 126970393, -21916710]]]
  g := ![![![-2395, 2911, 2679], ![775, -10093, 5590], ![37467, -98554, -4503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![3112390884041742011218645, -1309523279413140610172964, 226040427811406086356270]] ![![1732603, -103268889, -21619769]]
  ![![596365639, -250917933, 43311637]] where
 M := ![![![596365639, -250917933, 43311637]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![596365639, -250917933, 43311637]] ![![-47599, 2911, 2679]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB85I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB85I1 : PrimesBelowBoundCertificateInterval O 31 79 85 where
  m := 11
  g := ![1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB85I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![389017]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N0, I41N1, I47N1, I53N1, I59N1, I67N0, I67N1, I67N2, I79N0, I79N1, I79N2]
  Il := ![[], [I41N0, I41N1, I41N1], [], [I47N1], [I53N1], [I59N1], [], [I67N0, I67N1, I67N2], [], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
