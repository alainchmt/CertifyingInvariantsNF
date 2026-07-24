
import IdealArithmetic.Examples.NF3_1_87843_1.RI3_1_87843_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2236903, 8768, 82489]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![2236903, 8768, 82489]] 
 ![![37, 0, 0], ![0, 37, 0], ![32, 30, 1]] where
  M :=![![![2236903, 8768, 82489], ![2474670, 9700, 91257], ![2737710, 10731, 100957]]]
  hmulB := by decide  
  f := ![![![109, -41, -52]], ![![-1560, 1513, -93]], ![![-1246, 1217, -82]]]
  g := ![![![-10885, -66646, 82489], ![-12042, -73730, 91257], ![-13322, -81567, 100957]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [22, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 36], [0, 1]]
 g := ![![[3, 1], [33], [29, 33], [27], [1]], ![[11, 36], [33], [34, 4], [27], [1]]]
 h' := ![![[8, 36], [21, 36], [28, 25], [1, 12], [15, 8], [0, 1]], ![[0, 1], [13, 1], [6, 12], [23, 25], [5, 29], [8, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [12, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [22, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112, -80, -52]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 40, -52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, 41, 52]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-109, 41, 52]] 
 ![![37, 0, 0], ![6, 1, 0], ![1, 0, 1]] where
  M :=![![![-109, 41, 52], ![1560, -1513, 93], ![2790, -951, -1420]]]
  hmulB := by decide  
  f := ![![![-2236903, -8768, -82489]], ![![-429624, -1684, -15843]], ![![-134449, -527, -4958]]]
  g := ![![![-11, 41, 52], ![285, -1513, 93], ![268, -951, -1420]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![2236903, 8768, 82489]] ![![-109, 41, 52]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-460994249, 698082192, -254345294]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-460994249, 698082192, -254345294]] 
 ![![41, 0, 0], ![13, 1, 0], ![36, 0, 1]] where
  M :=![![![-460994249, 698082192, -254345294], ![-7630358820, 6406328689, 443736898], ![13312106940, -19611255066, 6850065587]]]
  hmulB := by decide  
  f := ![![![52586009180403350711, 206121635154032700, 1939184380291459982]], ![![18092528067170423383, 70917369988691617, 667187877054499328]], ![![47742817340436229416, 187137752616114006, 1760584746791999591]]]
  g := ![![![-9259321, 698082192, -254345294], ![-2607003905, 6406328689, 443736898], ![528196626, -19611255066, 6850065587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![134449, 527, 4958]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![134449, 527, 4958]] 
 ![![41, 0, 0], ![32, 1, 0], ![1, 0, 1]] where
  M :=![![![134449, 527, 4958], ![148740, 583, 5485], ![164550, 645, 6068]]]
  hmulB := by decide  
  f := ![![![-181, 74, 81]], ![![-82, 0, 67]], ![![109, -41, -52]]]
  g := ![![![2747, 527, 4958], ![3039, 583, 5485], ![3362, 645, 6068]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![372686014192649, 1460819176844, 13743330378925]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![372686014192649, 1460819176844, 13743330378925]] 
 ![![41, 0, 0], ![36, 1, 0], ![16, 0, 1]] where
  M :=![![![372686014192649, 1460819176844, 13743330378925], ![412299911367750, 1616093961674, 15204149555769], ![456124486673070, 1787873361987, 16820243517443]]]
  hmulB := by decide  
  f := ![![![11326579, -14765917, 4092586]], ![![12939864, -15384055, 3333165]], ![![-3389626, 4261045, -1082078]]]
  g := ![![![2443981408865, 1460819176844, 13743330378925], ![2703759411102, 1616093961674, 15204149555769], ![2991149984450, 1787873361987, 16820243517443]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-460994249, 698082192, -254345294]] ![![134449, 527, 4958]]
  ![![11326579, -14765917, 4092586]] where
 M := ![![![11326579, -14765917, 4092586]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![11326579, -14765917, 4092586]] ![![372686014192649, 1460819176844, 13743330378925]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [11, 38, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 17, 30], [31, 25, 13], [0, 1]]
 g := ![![[6, 10, 36], [41, 28, 6], [1, 11], [26, 8, 1], []], ![[4, 5, 22, 32], [39, 18, 38, 12], [17, 16], [39, 41, 21, 2], [7, 40]], ![[16, 15, 30, 40], [0, 38, 39, 36], [12, 31], [28, 4, 11, 16], [24, 40]]]
 h' := ![![[20, 17, 30], [22, 27, 6], [42, 26, 36], [15, 42, 22], [0, 0, 1], [0, 1]], ![[31, 25, 13], [6, 2, 14], [21, 22, 3], [6, 13, 4], [22, 17, 25], [20, 17, 30]], ![[0, 1], [10, 14, 23], [11, 38, 4], [10, 31, 17], [9, 26, 17], [31, 25, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 31], []]
 b := ![[], [8, 39, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [11, 38, 35, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21457, -32207, 11610]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![499, -749, 270]
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


def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -23, 2]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![23, -23, 2]] 
 ![![47, 0, 0], ![7, 1, 0], ![45, 0, 1]] where
  M :=![![![23, -23, 2], ![60, -31, -21], ![-630, 627, -52]]]
  hmulB := by decide  
  f := ![![![14779, 58, 545]], ![![2549, 10, 94]], ![![14535, 57, 536]]]
  g := ![![![2, -23, 2], ![26, -31, -21], ![-57, 627, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4877153, 19117, 179852]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![4877153, 19117, 179852]] 
 ![![47, 0, 0], ![32, 1, 0], ![10, 0, 1]] where
  M :=![![![4877153, 19117, 179852], ![5395560, 21149, 198969], ![5969070, 23397, 220118]]]
  hmulB := by decide  
  f := ![![![-2111, 1438, 425]], ![![-1166, 690, 329]], ![![740, -493, -159]]]
  g := ![![![52487, 19117, 179852], ![58066, 21149, 198969], ![64238, 23397, 220118]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![23, -23, 2]] ![![23, -23, 2]]
  ![![-2111, 1438, 425]] where
 M := ![![![-2111, 1438, 425]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-2111, 1438, 425]] ![![4877153, 19117, 179852]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9470659, 9785542, -1107145]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-9470659, 9785542, -1107145]] 
 ![![53, 0, 0], ![0, 53, 0], ![24, 40, 1]] where
  M :=![![![-9470659, 9785542, -1107145], ![-33214350, 20422256, 8678397], ![260351910, -267531069, 29100653]]]
  hmulB := by decide  
  f := ![![![-55019656829237, -215660815643, -2028928621798]], ![![-60867858653940, -238584040691, -2244589437441]], ![![-72123090437406, -282701227285, -2659642224508]]]
  g := ![![![322657, 1020214, -1107145], ![-4556526, -6164408, 8678397], ![-8265354, -27010513, 29100653]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [7, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 52], [0, 1]]
 g := ![![[11, 38], [43], [13, 40], [37], [29, 1]], ![[0, 15], [43], [7, 13], [37], [5, 52]]]
 h' := ![![[29, 52], [30, 41], [15, 34], [34, 26], [9, 39], [0, 1]], ![[0, 1], [0, 12], [47, 19], [46, 27], [27, 14], [29, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [34, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [7, 24, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2537, -47, 77]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, -59, 77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55019656829237, -215660815643, -2028928621798]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-55019656829237, -215660815643, -2028928621798]] 
 ![![53, 0, 0], ![12, 1, 0], ![15, 0, 1]] where
  M :=![![![-55019656829237, -215660815643, -2028928621798], ![-60867858653940, -238584040691, -2244589437441], ![-67337683123230, -263943843033, -2483173478132]]]
  hmulB := by decide  
  f := ![![![-9470659, 9785542, -1107145]], ![![-2770986, 2600920, -86931]], ![![2231925, -2278263, 235726]]]
  g := ![![![-415052787067, -215660815643, -2028928621798], ![-459169973661, -238584040691, -2244589437441], ![-507976506318, -263943843033, -2483173478132]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-9470659, 9785542, -1107145]] ![![-55019656829237, -215660815643, -2028928621798]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -2, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![29, -2, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![29, 57, 1]] where
  M :=![![![29, -2, 1], ![30, 2, -1], ![-30, 57, 1]]]
  hmulB := by decide  
  f := ![![![1, 1, 0]], ![![0, 1, 1]], ![![1, 1, 1]]]
  g := ![![![0, -1, 1], ![1, 1, -1], ![-1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [37, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 58], [0, 1]]
 g := ![![[29, 45], [48, 49], [12], [23, 35], [48, 1]], ![[6, 14], [40, 10], [12], [51, 24], [37, 58]]]
 h' := ![![[48, 58], [53, 35], [4, 7], [34, 22], [53, 25], [0, 1]], ![[0, 1], [22, 24], [45, 52], [28, 37], [14, 34], [48, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [31, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [37, 11, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![139, 202, -278]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139, 272, -278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![59, 0, 0], ![1, 1, 0], ![58, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![30, -27, 2]]]
  hmulB := by decide  
  f := ![![![29, -2, 1]], ![![1, 0, 0]], ![![28, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![-1, -27, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![29, -2, 1]] ![![1, 1, 0]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [1, 23, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 38, 31], [18, 22, 30], [0, 1]]
 g := ![![[27], [57, 49], [53, 45, 25], [55, 51, 20], [1]], ![[24, 34, 30, 11], [3, 52], [37, 33, 56, 24], [58, 55, 55, 8], [12, 36, 35, 23]], ![[11, 4, 26, 50], [60, 5], [51, 0, 47, 17], [22, 48, 53, 18], [33, 1, 10, 38]]]
 h' := ![![[34, 38, 31], [7, 37], [8, 53, 7], [6, 27, 5], [60, 38, 52], [0, 1]], ![[18, 22, 30], [45, 3, 49], [29, 40, 28], [44, 43, 32], [8, 17, 4], [34, 38, 31]], ![[0, 1], [2, 21, 12], [60, 29, 26], [22, 52, 24], [4, 6, 5], [18, 22, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 6], []]
 b := ![[], [10, 55, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [1, 23, 9, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3721, -2501, -793]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![61, -41, -13]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![580227619, 892666376, -1280985791]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![580227619, 892666376, -1280985791]] 
 ![![67, 0, 0], ![0, 67, 0], ![8, 53, 1]] where
  M :=![![![580227619, 892666376, -1280985791], ![-38429573730, 35166843976, -388319415], ![-11649582450, -27944949525, 34778524561]]]
  hmulB := by decide  
  f := ![![![18092528067170423383, 70917369988691617, 667187877054499328]], ![![20015636311634979840, 78455386698941527, 738105247043190945]], ![![18324061290527060402, 71824911886899376, 675725996171152943]]]
  g := ![![![161613641, 1026640497, -1280985791], ![-527209230, 832056313, -388319415], ![-4326534014, -27928458974, 34778524561]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [33, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 66], [0, 1]]
 g := ![![[25, 65], [31, 60], [37], [23], [39], [1]], ![[0, 2], [44, 7], [37], [23], [39], [1]]]
 h' := ![![[46, 66], [49, 47], [20, 44], [54, 38], [3, 31], [34, 46], [0, 1]], ![[0, 1], [0, 20], [34, 23], [60, 29], [22, 36], [6, 21], [46, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [24, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [33, 21, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1225, -586, 396]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -322, 396]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18092528067170423383, 70917369988691617, 667187877054499328]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![18092528067170423383, 70917369988691617, 667187877054499328]] 
 ![![67, 0, 0], ![13, 1, 0], ![32, 0, 1]] where
  M :=![![![18092528067170423383, 70917369988691617, 667187877054499328], ![20015636311634979840, 78455386698941527, 738105247043190945], ![22143157411295728350, 86794641468824325, 816560633742132472]]]
  hmulB := by decide  
  f := ![![![580227619, 892666376, -1280985791]], ![![-460994249, 698082192, -254345294]], ![![103249274, 9259321, -92731653]]]
  g := ![![![-62379250872038002, 70917369988691617, 667187877054499328], ![-69009725684080153, 78455386698941527, 738105247043190945], ![-76344973246973537, 86794641468824325, 816560633742132472]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![580227619, 892666376, -1280985791]] ![![18092528067170423383, 70917369988691617, 667187877054499328]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113980083476707387, 446768285849827, 4203178772971346]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![113980083476707387, 446768285849827, 4203178772971346]] 
 ![![71, 0, 0], ![0, 71, 0], ![49, 17, 1]] where
  M :=![![![113980083476707387, 446768285849827, 4203178772971346], ![126095363189140380, 494256606481045, 4649947058821173], ![139498411764635190, 546792600968709, 5144203665302218]]]
  hmulB := by decide  
  f := ![![![56532143, -42512732, -7762669]], ![![-232880070, 266124206, -50275401]], ![![-37988003, 50218921, -14354983]]]
  g := ![![![-1295432061956177, -1000102406403705, 4203178772971346], ![-1433127361874607, -1106406244978576, 4649947058821173], ![-1585458701903852, -1224009432523507, 5144203665302218]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [46, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 70], [0, 1]]
 g := ![![[30, 16], [35, 4], [19, 16], [48], [38], [1]], ![[31, 55], [53, 67], [20, 55], [48], [38], [1]]]
 h' := ![![[40, 70], [23, 67], [49, 69], [20, 4], [13, 41], [25, 40], [0, 1]], ![[0, 1], [5, 4], [40, 2], [38, 67], [20, 30], [63, 31], [40, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [61, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [46, 31, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134, 252, -52]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, 16, -52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56532143, -42512732, -7762669]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![56532143, -42512732, -7762669]] 
 ![![71, 0, 0], ![53, 1, 0], ![31, 0, 1]] where
  M :=![![![56532143, -42512732, -7762669], ![-232880070, 266124206, -50275401], ![-1508262030, 1124555757, 215848805]]]
  hmulB := by decide  
  f := ![![![113980083476707387, 446768285849827, 4203178772971346]], ![![86859715316262421, 340464447274956, 3203076366567641]], ![![51730718303416397, 202769147356526, 1907644304611464]]]
  g := ![![![35920418, -42512732, -7762669], ![-179984867, 266124206, -50275401], ![-954944086, 1124555757, 215848805]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![113980083476707387, 446768285849827, 4203178772971346]] ![![56532143, -42512732, -7762669]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [55, 22, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 48, 35], [23, 24, 38], [0, 1]]
 g := ![![[1, 49, 4], [31, 37], [72, 50], [46, 3, 35], [41, 1], []], ![[46, 43, 40, 61], [60, 50], [70, 70], [14, 54, 50, 37], [70, 65], [3, 57]], ![[41, 5, 28, 72], [67, 4], [19, 12], [58, 61, 23, 27], [9, 41], [0, 57]]]
 h' := ![![[18, 48, 35], [65, 47, 71], [23, 22, 16], [25, 55, 59], [8, 65, 53], [0, 0, 1], [0, 1]], ![[23, 24, 38], [9, 19, 64], [43, 45, 59], [30, 48, 56], [42, 22, 43], [13, 60, 24], [18, 48, 35]], ![[0, 1], [15, 7, 11], [14, 6, 71], [16, 43, 31], [48, 59, 50], [18, 13, 48], [23, 24, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 60], []]
 b := ![[], [39, 7, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [55, 22, 32, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6935, 4453, 2117]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-95, 61, 29]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [44, 22, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 71, 9], [48, 7, 70], [0, 1]]
 g := ![![[0, 45, 13], [28, 53, 4], [64, 37, 49], [65, 67, 2], [48, 1], []], ![[42, 72, 17, 73], [41, 57, 32, 76], [47, 45, 76, 62], [6, 28, 22, 18], [25, 49], [31, 2]], ![[15, 17, 3, 41], [52, 51, 73, 57], [12, 28, 45, 7], [20, 9, 38, 7], [74, 64], [49, 2]]]
 h' := ![![[0, 71, 9], [32, 48, 31], [28, 64, 2], [63, 13, 72], [21, 6, 70], [0, 0, 1], [0, 1]], ![[48, 7, 70], [13, 78, 17], [65, 2, 37], [52, 72, 68], [52, 9, 70], [58, 20, 7], [0, 71, 9]], ![[0, 1], [51, 32, 31], [78, 13, 40], [46, 73, 18], [4, 64, 18], [69, 59, 71], [48, 7, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 16], []]
 b := ![[], [30, 65, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [44, 22, 31, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36340, -21488, -9480]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![460, -272, -120]
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



lemma PB84I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB84I1 : PrimesBelowBoundCertificateInterval O 31 79 84 where
  m := 11
  g := ![2, 3, 1, 3, 2, 2, 1, 2, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB84I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
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
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
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
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
      exact NI59N1
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
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N0, I41N1, I41N2, I47N0, I47N1, I53N1, I59N1, I67N1, I71N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [], [I47N0, I47N0, I47N1], [I53N1], [I59N1], [], [I67N1], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
