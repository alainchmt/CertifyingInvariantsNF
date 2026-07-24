
import IdealArithmetic.Examples.NF3_1_702351_1.RI3_1_702351_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5195, -87, -306]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![5195, -87, -306]] 
 ![![37, 0, 0], ![0, 37, 0], ![17, 5, 1]] where
  M :=![![![5195, -87, -306], ![-49440, 5108, -303], ![69, -7038, 5282]]]
  hmulB := by decide  
  f := ![![![-671566, -70626, -42957]], ![![-7057329, -742192, -451425]], ![![-1516163, -159449, -96982]]]
  g := ![![![281, 39, -306], ![-1197, 179, -303], ![-2425, -904, 5282]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [23, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 36], [0, 1]]
 g := ![![[], [26], [], [], [1]], ![[], [26], [], [], [1]]]
 h' := ![![[0, 36], [31], [0, 10], [11], [14], [0, 1]], ![[0, 1], [31], [0, 27], [11], [14], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [0, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [23, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2289, 1139, 28]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49, 27, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![671566, 70626, 42957]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![671566, 70626, 42957]] 
 ![![37, 0, 0], ![3, 1, 0], ![25, 0, 1]] where
  M :=![![![671566, 70626, 42957], ![7057329, 742192, 451425], ![9394764, 988011, 600940]]]
  hmulB := by decide  
  f := ![![![-5195, 87, 306]], ![![915, -131, 33]], ![![-3512, 249, 64]]]
  g := ![![![-16601, 70626, 42957], ![-174456, 742192, 451425], ![-232237, 988011, 600940]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![5195, -87, -306]] ![![671566, 70626, 42957]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [18, 4, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 39, 15], [19, 1, 26], [0, 1]]
 g := ![![[23, 38, 21], [29, 5], [2, 4], [16, 15, 1], []], ![[34, 31, 7, 17], [11, 37], [22, 18], [10, 8, 12, 15], [35, 20]], ![[3, 6, 35, 27], [28, 18], [22, 21], [26, 31, 18, 22], [24, 20]]]
 h' := ![![[37, 39, 15], [6, 3, 29], [6, 14, 13], [40, 35, 39], [0, 0, 1], [0, 1]], ![[19, 1, 26], [23, 21, 33], [4, 35, 18], [21, 37, 31], [1, 8, 1], [37, 39, 15]], ![[0, 1], [13, 17, 20], [5, 33, 10], [27, 10, 12], [11, 33, 39], [19, 1, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 3], []]
 b := ![[], [0, 9, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [18, 4, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20985645, 305532, -396306]
  a := ![5, 0, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![511845, 7452, -9666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [28, 3, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 1, 30], [9, 41, 13], [0, 1]]
 g := ![![[12, 19, 24], [1, 3, 23], [3, 14], [28, 17, 1], []], ![[35, 4, 19, 37], [6, 22, 33, 30], [1, 6], [15, 42, 35, 34], [9, 40]], ![[27, 39, 21, 10], [42, 20, 10, 16], [6, 9], [38, 8, 41, 13], [26, 40]]]
 h' := ![![[8, 1, 30], [15, 40, 29], [16, 6, 25], [33, 42, 10], [0, 0, 1], [0, 1]], ![[9, 41, 13], [0, 7, 24], [8, 25, 1], [37, 41, 36], [27, 30, 41], [8, 1, 30]], ![[0, 1], [16, 39, 33], [20, 12, 17], [4, 3, 40], [41, 13, 1], [9, 41, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 11], []]
 b := ![[], [7, 30, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [28, 3, 26, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29827510419, -377586612, -685298654]
  a := ![-66, -64, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-693663033, -8781084, -15937178]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [12, 10, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 40, 21], [3, 6, 26], [0, 1]]
 g := ![![[25, 39, 3], [40, 15, 42], [23, 35, 37], [27, 32, 1], []], ![[34, 9, 44, 14], [17, 8, 19, 2], [40, 40, 35, 27], [37, 25, 18, 4], [0, 18]], ![[28, 28, 28, 5], [42, 30, 22, 46], [23, 3, 34, 26], [2, 44, 22, 5], [42, 18]]]
 h' := ![![[29, 40, 21], [37, 20, 35], [6, 33, 29], [5, 4, 15], [0, 0, 1], [0, 1]], ![[3, 6, 26], [19, 39, 19], [19, 14, 21], [46, 42, 33], [42, 36, 6], [29, 40, 21]], ![[0, 1], [21, 35, 40], [38, 0, 44], [18, 1, 46], [22, 11, 40], [3, 6, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 18], []]
 b := ![[], [19, 19, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [12, 10, 15, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21632831, 13724, 247032]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-460273, 292, 5256]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1014977406962782, -106741249315045, -64923453972122]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-1014977406962782, -106741249315045, -64923453972122]] 
 ![![53, 0, 0], ![0, 53, 0], ![52, 47, 1]] where
  M :=![![![-1014977406962782, -106741249315045, -64923453972122], ![-10666158588141732, -1121718656277827, -682265291233193], ![-14198862257004633, -1493239441358806, -908236157647737]]]
  hmulB := by decide  
  f := ![![![-17731697, -1488739, 2385853]], ![![381144855, -19220436, -12807026]], ![![314006108, -17469817, -9322808]]]
  g := ![![![44547966029954, 55559643158013, -64923453972122], ![468144085961968, 583863208144948, -682265291233193], ![623196564918447, 777242640907261, -908236157647737]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [3, 2, 1] where
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
 g := ![![[36, 44], [42], [36, 47], [1], [51, 1]], ![[1, 9], [42], [48, 6], [1], [49, 52]]]
 h' := ![![[51, 52], [37, 16], [51, 28], [33, 10], [6, 1], [0, 1]], ![[0, 1], [5, 37], [48, 25], [13, 43], [4, 52], [51, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [40, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [3, 2, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2265, 1135, 14]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 9, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17731697, -1488739, 2385853]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-17731697, -1488739, 2385853]] 
 ![![53, 0, 0], ![43, 1, 0], ![48, 0, 1]] where
  M :=![![![-17731697, -1488739, 2385853], ![381144855, -19220436, -12807026], ![-349436217, 54874619, -16242958]]]
  hmulB := by decide  
  f := ![![![-1014977406962782, -106741249315045, -64923453972122]], ![![-1024720511085686, -107765893902354, -65546675698763]], ![![-1187127882853173, -124845649216622, -75935131100181]]]
  g := ![![![-1287488, -1488739, 2385853], ![34384167, -19220436, -12807026], ![-36403450, 54874619, -16242958]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-1014977406962782, -106741249315045, -64923453972122]] ![![-17731697, -1488739, 2385853]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![395185364795, 41560116767, 25278196998]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![395185364795, 41560116767, 25278196998]] 
 ![![59, 0, 0], ![0, 59, 0], ![54, 50, 1]] where
  M :=![![![395185364795, 41560116767, 25278196998], ![4152909950212, 436745481562, 265642620371], ![5528381737579, 581398530954, 353625248028]]]
  hmulB := by decide  
  f := ![![![616878, -61176, 1859]], ![![176947, 555702, -430091]], ![![546168, 415667, -351290]]]
  g := ![![![-16437919883, -20717792087, 25278196998], ![-172742229658, -217718398932, 265642620371], ![-229955621287, -289828201194, 353625248028]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [26, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 58], [0, 1]]
 g := ![![[54, 25], [34, 7], [36], [], [12, 1]], ![[0, 34], [0, 52], [36], [], [24, 58]]]
 h' := ![![[12, 58], [1, 54], [8, 19], [0, 53], [42], [0, 1]], ![[0, 1], [0, 5], [0, 40], [46, 6], [42], [12, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [18, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [26, 47, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64078, 3854, 3197]
  a := ![3, 21, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1840, -2644, 3197]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![616878, -61176, 1859]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![616878, -61176, 1859]] 
 ![![59, 0, 0], ![5, 1, 0], ![55, 0, 1]] where
  M :=![![![616878, -61176, 1859], ![176947, 555702, -430091], ![-9934850, 42757, 678054]]]
  hmulB := by decide  
  f := ![![![395185364795, 41560116767, 25278196998]], ![![103878589393, 10924509583, 6644637379]], ![![462094522056, 48596694121, 29558069202]]]
  g := ![![![13907, -61176, 1859], ![356838, 555702, -430091], ![-804095, 42757, 678054]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![395185364795, 41560116767, 25278196998]] ![![616878, -61176, 1859]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39083546, -11160645, 11177665]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-39083546, -11160645, 11177665]] 
 ![![61, 0, 0], ![28, 1, 0], ![15, 0, 1]] where
  M :=![![![-39083546, -11160645, 11177665], ![1777282775, -50244191, -89302180], ![-2311036435, 257086295, -27922901]]]
  hmulB := by decide  
  f := ![![![-24361330162741191, -2561986896170030, -1558282663900115]], ![![-15379093889131343, -1617359838552001, -983730167188415]], ![![-11577358035821105, -1217545978889395, -740550544673326]]]
  g := ![![![1733599, -11160645, 11177665], ![74158243, -50244191, -89302180], ![-149026380, 257086295, -27922901]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-172150475890391, -18104399901577, -11011677128059]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-172150475890391, -18104399901577, -11011677128059]] 
 ![![61, 0, 0], ![42, 1, 0], ![56, 0, 1]] where
  M :=![![![-172150475890391, -18104399901577, -11011677128059], ![-1809088817420653, -190254875791968, -115719122182980], ![-2408271236263183, -253268573945357, -154046075988814]]]
  hmulB := by decide  
  f := ![![![116377908, -4512385, -4929348]], ![![66970858, -1273027, -3830983]], ![![98646211, -6001124, -2543495]]]
  g := ![![![19752266215527, -18104399901577, -11011677128059], ![207571914886703, -190254875791968, -115719122182980], ![276321133193695, -253268573945357, -154046075988814]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -5, -3]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-47, -5, -3]] 
 ![![61, 0, 0], ![52, 1, 0], ![51, 0, 1]] where
  M :=![![![-47, -5, -3], ![-493, -52, -32], ![-667, -69, -42]]]
  hmulB := by decide  
  f := ![![![24, 3, -4]], ![![10, 3, -3]], ![![31, 1, -3]]]
  g := ![![![6, -5, -3], ![63, -52, -32], ![83, -69, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-39083546, -11160645, 11177665]] ![![-172150475890391, -18104399901577, -11011677128059]]
  ![![-24, -3, 4]] where
 M := ![![![-24, -3, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-24, -3, 4]] ![![-47, -5, -3]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [16, 29, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 39, 3], [34, 27, 64], [0, 1]]
 g := ![![[32, 11, 21], [42, 5, 4], [6, 40], [5, 24], [58, 1], []], ![[40, 19, 0, 31], [13, 21, 19, 3], [21, 6], [40, 25], [47, 59], [19, 9]], ![[51, 18, 8, 64], [46, 50, 46, 40], [40, 21], [55, 65], [30, 47], [25, 9]]]
 h' := ![![[24, 39, 3], [65, 65, 17], [36, 27, 2], [20, 16, 24], [10, 44, 52], [0, 0, 1], [0, 1]], ![[34, 27, 64], [18, 32, 51], [22, 57, 1], [31, 62, 26], [1, 7, 62], [4, 38, 27], [24, 39, 3]], ![[0, 1], [52, 37, 66], [54, 50, 64], [15, 56, 17], [15, 16, 20], [19, 29, 39], [34, 27, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 6], []]
 b := ![[], [14, 52, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [16, 29, 9, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3683258, -11725, 117250]
  a := ![-3, 1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54974, -175, 1750]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-622, -866, 695]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-622, -866, 695]] 
 ![![71, 0, 0], ![0, 71, 0], ![32, 53, 1]] where
  M :=![![![-622, -866, 695], ![110163, -1488, -6757], ![-171396, 15985, 244]]]
  hmulB := by decide  
  f := ![![![-1516163, -159449, -96982]], ![![-15933000, -1675612, -1019161]], ![![-12875723, -1354090, -823601]]]
  g := ![![![-322, -531, 695], ![4597, 5023, -6757], ![-2524, 43, 244]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [63, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 70], [0, 1]]
 g := ![![[41, 5], [9, 32], [18, 36], [58], [19], [1]], ![[48, 66], [68, 39], [40, 35], [58], [19], [1]]]
 h' := ![![[44, 70], [1, 17], [2, 23], [47, 6], [3, 49], [8, 44], [0, 1]], ![[0, 1], [39, 54], [20, 48], [27, 65], [29, 22], [27, 27], [44, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [12, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [63, 27, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4713, 4622, 469]
  a := ![4, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-145, -285, 469]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1516163, 159449, 96982]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1516163, 159449, 96982]] 
 ![![71, 0, 0], ![56, 1, 0], ![21, 0, 1]] where
  M :=![![![1516163, 159449, 96982], ![15933000, 1675612, 1019161], ![21210117, 2230586, 1356714]]]
  hmulB := by decide  
  f := ![![![622, 866, -695]], ![![-1061, 704, -453]], ![![2598, 31, -209]]]
  g := ![![![-133093, 159449, 96982], ![-1398643, 1675612, 1019161], ![-1861883, 2230586, 1356714]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-622, -866, 695]] ![![1516163, 159449, 96982]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [64, 32, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 71, 66], [38, 1, 7], [0, 1]]
 g := ![![[59, 69, 61], [33, 24], [25, 37], [70, 56, 19], [58, 1], []], ![[14, 59, 22, 30], [43, 70], [22, 19], [59, 7, 42, 68], [38, 1], [23, 49]], ![[6, 42, 65, 47], [19, 19], [5, 12], [31, 48, 18, 47], [46, 4], [9, 49]]]
 h' := ![![[20, 71, 66], [30, 7, 39], [5, 19, 43], [46, 64, 57], [11, 51, 47], [0, 0, 1], [0, 1]], ![[38, 1, 7], [45, 34, 63], [60, 43, 56], [9, 32, 47], [68, 12, 55], [23, 63, 1], [20, 71, 66]], ![[0, 1], [57, 32, 44], [18, 11, 47], [51, 50, 42], [40, 10, 44], [65, 10, 71], [38, 1, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 69], []]
 b := ![[], [34, 44, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [64, 32, 15, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12612721, -103660, -310980]
  a := ![-5, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-172777, -1420, -4260]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [17, 3, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 48, 76], [61, 30, 3], [0, 1]]
 g := ![![[49, 72, 51], [53, 44, 50], [27, 11, 26], [70, 56, 25], [18, 1], []], ![[11, 51, 76, 11], [31, 23, 43, 21], [8, 4, 17, 65], [56, 21, 50, 9], [60, 31], [32, 9]], ![[51, 3, 30, 30], [15, 8, 31, 6], [28, 58, 19, 37], [69, 58, 31, 54], [67, 13], [26, 9]]]
 h' := ![![[36, 48, 76], [47, 29, 29], [15, 73, 45], [74, 44, 37], [10, 8, 5], [0, 0, 1], [0, 1]], ![[61, 30, 3], [68, 69, 72], [64, 10, 25], [15, 59, 30], [29, 66, 47], [41, 47, 30], [36, 48, 76]], ![[0, 1], [53, 60, 57], [27, 75, 9], [51, 55, 12], [66, 5, 27], [40, 32, 48], [61, 30, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 71], []]
 b := ![[], [57, 29, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [17, 3, 61, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24203151, 1237298, -1653312]
  a := ![6, -6, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![306369, 15662, -20928]
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



lemma PB238I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB238I1 : PrimesBelowBoundCertificateInterval O 31 79 238 where
  m := 11
  g := ![2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB238I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I53N1, I59N1, I61N0, I61N1, I61N2, I71N1]
  Il := ![[I37N1], [], [], [], [I53N1], [I59N1], [I61N0, I61N1, I61N2], [], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
