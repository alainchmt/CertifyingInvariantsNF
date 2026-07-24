
import IdealArithmetic.Examples.NF3_3_376329_1.RI3_3_376329_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-185217341, 9225556, 2737598]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-185217341, 9225556, 2737598]] 
 ![![37, 0, 0], ![0, 37, 0], ![29, 10, 1]] where
  M :=![![![-185217341, 9225556, 2737598], ![-1248344688, 62179241, 18451112], ![-3582681192, 178451028, 52953685]]]
  hmulB := by decide  
  f := ![![![-1008377, 243868, -32842]], ![![14975952, -3621763, 487736]], ![![49319, -11918, 1603]]]
  g := ![![![-7151559, -490552, 2737598], ![-48200728, -3306267, 18451112], ![-138333461, -9488806, 52953685]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [23, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 36], [0, 1]]
 g := ![![[22, 12], [30], [8, 27], [33], [1]], ![[18, 25], [30], [36, 10], [33], [1]]]
 h' := ![![[12, 36], [14, 30], [1, 20], [29, 29], [14, 12], [0, 1]], ![[0, 1], [4, 7], [19, 17], [7, 8], [10, 25], [12, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [23, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [23, 25, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3397, -1054, 716]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-653, -222, 716]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1008377, 243868, -32842]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-1008377, 243868, -32842]] 
 ![![37, 0, 0], ![17, 1, 0], ![32, 0, 1]] where
  M :=![![![-1008377, 243868, -32842], ![14975952, -3621763, 487736], ![-118691784, 28704492, -3865631]]]
  hmulB := by decide  
  f := ![![![-185217341, 9225556, 2737598]], ![![-118838905, 5919289, 1756494]], ![![-257017192, 12801860, 3798833]]]
  g := ![![![-110897, 243868, -32842], ![1646983, -3621763, 487736], ![-13053188, 28704492, -3865631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-185217341, 9225556, 2737598]] ![![-1008377, 243868, -32842]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1341301, 324380, -43684]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-1341301, 324380, -43684]] 
 ![![41, 0, 0], ![16, 1, 0], ![28, 0, 1]] where
  M :=![![![-1341301, 324380, -43684], ![19919904, -4817429, 648760], ![-157877232, 38181012, -5141809]]]
  hmulB := by decide  
  f := ![![![13556059, -675212, -200364]], ![![7518608, -374493, -111128]], ![![15653252, -779668, -231361]]]
  g := ![![![-129469, 324380, -43684], ![1922768, -4817429, 648760], ![-15239092, 38181012, -5141809]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9731, -484, -144]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![9731, -484, -144]] 
 ![![41, 0, 0], ![25, 1, 0], ![3, 0, 1]] where
  M :=![![![9731, -484, -144], ![65664, -3281, -968], ![187872, -9276, -2797]]]
  hmulB := by decide  
  f := ![![![-197789, 18004, 3952]], ![![-164557, 14979, 3288]], ![![-192735, 17544, 3851]]]
  g := ![![![543, -484, -144], ![3673, -3281, -968], ![10443, -9276, -2797]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2560001, 127512, 37838]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-2560001, 127512, 37838]] 
 ![![41, 0, 0], ![40, 1, 0], ![0, 0, 1]] where
  M :=![![![-2560001, 127512, 37838], ![-17254128, 859417, 255024], ![-49518408, 2466480, 731905]]]
  hmulB := by decide  
  f := ![![![-3865, 120, 158]], ![![-5528, 361, 160]], ![![-456, -624, 241]]]
  g := ![![![-186841, 127512, 37838], ![-1259288, 859417, 255024], ![-3614088, 2466480, 731905]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-1341301, 324380, -43684]] ![![9731, -484, -144]]
  ![![40887841, -9888312, 1331652]] where
 M := ![![![40887841, -9888312, 1331652]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![40887841, -9888312, 1331652]] ![![-2560001, 127512, 37838]]
  ![![41, 0, 0]] where
 M := ![![![54079, -27552, 5330]]]
 hmul := by decide  
 g := ![![![![1319, -672, 130]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [20, 21, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 17, 20], [41, 25, 23], [0, 1]]
 g := ![![[34, 22, 10], [33, 2, 9], [26, 40], [15, 6, 1], []], ![[13, 41, 32, 2], [24, 9, 27, 37], [27, 25], [38, 8, 13, 30], [27, 13]], ![[26, 33, 19, 10], [4, 22, 23, 16], [33, 21], [31, 38, 33, 25], [24, 13]]]
 h' := ![![[8, 17, 20], [28, 7, 28], [40, 20, 3], [1, 38, 30], [0, 0, 1], [0, 1]], ![[41, 25, 23], [0, 16, 23], [19, 8, 2], [0, 35, 5], [40, 4, 25], [8, 17, 20]], ![[0, 1], [16, 20, 35], [34, 15, 38], [7, 13, 8], [40, 39, 17], [41, 25, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 8], []]
 b := ![[], [41, 3, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [20, 21, 37, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6018323, -2280333, 526406]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139961, -53031, 12242]
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


def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11711, 1066, 234]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-11711, 1066, 234]] 
 ![![47, 0, 0], ![12, 1, 0], ![16, 0, 1]] where
  M :=![![![-11711, 1066, 234], ![-106704, 9713, 2132], ![-432744, 39390, 8647]]]
  hmulB := by decide  
  f := ![![![8831, -442, -130]], ![![3516, -175, -52]], ![![6664, -338, -97]]]
  g := ![![![-601, 1066, 234], ![-5476, 9713, 2132], ![-22208, 39390, 8647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-935, 48, 14]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-935, 48, 14]] 
 ![![47, 0, 0], ![22, 1, 0], ![29, 0, 1]] where
  M :=![![![-935, 48, 14], ![-6384, 331, 96], ![-18696, 984, 283]]]
  hmulB := by decide  
  f := ![![![791, -192, 26]], ![![118, -29, 4]], ![![2477, -600, 81]]]
  g := ![![![-51, 48, 14], ![-350, 331, 96], ![-1033, 984, 283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-11711, 1066, 234]] ![![-11711, 1066, 234]]
  ![![-77861039, 7087392, 1555736]] where
 M := ![![![-77861039, 7087392, 1555736]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-77861039, 7087392, 1555736]] ![![-935, 48, 14]]
  ![![47, 0, 0]] where
 M := ![![![-1531879319, 139441104, 30608374]]]
 hmul := by decide  
 g := ![![![![-32593177, 2966832, 651242]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [19, 31, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 13, 34], [12, 39, 19], [0, 1]]
 g := ![![[45, 49, 49], [44, 7], [30, 29, 42], [27, 25], [1]], ![[23, 15, 2, 51], [25, 46], [11, 51, 19, 19], [18, 15], [3, 48, 30, 31]], ![[38, 16, 12, 41], [29, 4], [1, 43, 15, 51], [15, 36], [34, 7, 0, 22]]]
 h' := ![![[46, 13, 34], [22, 14, 46], [13, 52, 22], [7, 25, 25], [34, 22, 5], [0, 1]], ![[12, 39, 19], [51, 3, 44], [7, 12, 29], [22, 33, 23], [24, 5, 42], [46, 13, 34]], ![[0, 1], [4, 36, 16], [48, 42, 2], [40, 48, 5], [22, 26, 6], [12, 39, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 23], []]
 b := ![[], [37, 43, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [19, 31, 48, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-224137, 72504, -26500]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4229, 1368, -500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [43, 53, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 23, 35], [15, 35, 24], [0, 1]]
 g := ![![[48, 32, 41], [41, 47, 5], [40, 21], [10, 40, 20], [1]], ![[56, 39, 39, 45], [32, 51, 10, 49], [54, 5], [20, 33, 19, 20], [57, 49, 44, 41]], ![[30, 19, 49, 18], [48, 37, 13, 44], [45, 45], [50, 43, 19, 50], [8, 31, 57, 18]]]
 h' := ![![[1, 23, 35], [7, 43, 49], [44, 50, 51], [42, 12, 27], [16, 6, 16], [0, 1]], ![[15, 35, 24], [2, 26, 34], [32, 2, 54], [42, 50, 8], [28, 15, 3], [1, 23, 35]], ![[0, 1], [26, 49, 35], [10, 7, 13], [36, 56, 24], [22, 38, 40], [15, 35, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 6], []]
 b := ![[], [34, 2, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [43, 53, 43, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9674584, 3662130, -816973]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-163976, 62070, -13847]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [47, 49, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 28, 50], [46, 32, 11], [0, 1]]
 g := ![![[29, 57, 45], [2, 16], [58, 47, 60], [23, 60, 15], [1]], ![[43, 50, 30, 40], [22, 60], [40, 14, 10, 11], [49, 53, 17, 23], [47, 21, 8, 11]], ![[4, 2, 3, 18], [41, 49], [55, 25, 37, 17], [9, 37, 43, 17], [38, 30, 56, 50]]]
 h' := ![![[40, 28, 50], [23, 35, 44], [19, 57, 4], [17, 31, 11], [14, 12, 25], [0, 1]], ![[46, 32, 11], [23, 23, 47], [9, 45, 50], [53, 34, 11], [59, 21, 58], [40, 28, 50]], ![[0, 1], [52, 3, 31], [24, 20, 7], [26, 57, 39], [24, 28, 39], [46, 32, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 51], []]
 b := ![[], [22, 58, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [47, 49, 36, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1316197, 638060, -163846]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21577, 10460, -2686]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1728113, -412962, 54552]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![1728113, -412962, 54552]] 
 ![![67, 0, 0], ![0, 67, 0], ![37, 21, 1]] where
  M :=![![![1728113, -412962, 54552], ![-24875712, 6061175, -825924], ![200748528, -48365550, 6474137]]]
  hmulB := by decide  
  f := ![![![10528226675, -524404182, -155612064]], ![![70959101184, -3534427075, -1048808364]], ![![31094541317, -1548799053, -459591715]]]
  g := ![![![-4333, -23262, 54552], ![84828, 349337, -825924], ![-579023, -2751081, 6474137]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [65, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 66], [0, 1]]
 g := ![![[49, 33], [46, 21], [64], [17], [23], [1]], ![[0, 34], [27, 46], [64], [17], [23], [1]]]
 h' := ![![[31, 66], [25, 10], [4, 50], [55, 8], [50, 33], [2, 31], [0, 1]], ![[0, 1], [0, 57], [13, 17], [35, 59], [1, 34], [25, 36], [31, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [1, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [65, 36, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-282390, -26308, 39965]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26285, -12919, 39965]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10528226675, 524404182, 155612064]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-10528226675, 524404182, 155612064]] 
 ![![67, 0, 0], ![25, 1, 0], ![10, 0, 1]] where
  M :=![![![-10528226675, 524404182, 155612064], ![-70959101184, 3534427075, 1048808364], ![-203648756400, 10143613242, 3010022893]]]
  hmulB := by decide  
  f := ![![![-1728113, 412962, -54552]], ![![-273539, 63625, -8028]], ![![-3254174, 783510, -104771]]]
  g := ![![![-376036595, 524404182, 155612064], ![-2534445697, 3534427075, 1048808364], ![-7273721140, 10143613242, 3010022893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![1728113, -412962, 54552]] ![![-10528226675, 524404182, 155612064]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163279, 14864, 3262]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-163279, 14864, 3262]] 
 ![![71, 0, 0], ![6, 1, 0], ![50, 0, 1]] where
  M :=![![![-163279, 14864, 3262], ![-1487472, 135379, 29728], ![-6034248, 549432, 120515]]]
  hmulB := by decide  
  f := ![![![18314311, -912224, -270694]], ![![3286230, -163685, -48572]], ![![17886922, -890936, -264377]]]
  g := ![![![-5853, 14864, 3262], ![-53326, 135379, 29728], ![-216290, 549432, 120515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![118537, -5904, -1752]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![118537, -5904, -1752]] 
 ![![71, 0, 0], ![66, 1, 0], ![61, 0, 1]] where
  M :=![![![118537, -5904, -1752], ![798912, -39791, -11808], ![2292768, -114192, -33887]]]
  hmulB := by decide  
  f := ![![![-18481, 4464, -600]], ![![-13326, 3217, -432]], ![![-46475, 11232, -1511]]]
  g := ![![![8663, -5904, -1752], ![58386, -39791, -11808], ![167557, -114192, -33887]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7207, 656, 144]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-7207, 656, 144]] 
 ![![71, 0, 0], ![69, 1, 0], ![70, 0, 1]] where
  M :=![![![-7207, 656, 144], ![-65664, 5977, 1312], ![-266304, 24240, 5321]]]
  hmulB := by decide  
  f := ![![![-737, 16, 16]], ![![-819, 25, 16]], ![![-778, -16, 25]]]
  g := ![![![-881, 656, 144], ![-8027, 5977, 1312], ![-32554, 24240, 5321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-163279, 14864, 3262]] ![![118537, -5904, -1752]]
  ![![-565639, 51488, 11302]] where
 M := ![![![-565639, 51488, 11302]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-565639, 51488, 11302]] ![![-7207, 656, 144]]
  ![![71, 0, 0]] where
 M := ![![![-2314115567, 210645072, 46238182]]]
 hmul := by decide  
 g := ![![![![-32593177, 2966832, 651242]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7394357, 368308, 109292]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-7394357, 368308, 109292]] 
 ![![73, 0, 0], ![0, 73, 0], ![56, 22, 1]] where
  M :=![![![-7394357, 368308, 109292], ![-49837152, 2482355, 736616], ![-143029872, 7124220, 2114047]]]
  hmulB := by decide  
  f := ![![![-9605, 2332, -316]], ![![144096, -34765, 4664]], ![![20504, -4922, 655]]]
  g := ![![![-185133, -27892, 109292], ![-1247776, -187989, 736616], ![-3581048, -539518, 2114047]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [51, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 72], [0, 1]]
 g := ![![[14, 35], [4], [54], [66, 32], [37], [1]], ![[63, 38], [4], [54], [67, 41], [37], [1]]]
 h' := ![![[16, 72], [63, 20], [11, 71], [65, 45], [57, 55], [22, 16], [0, 1]], ![[0, 1], [18, 53], [52, 2], [55, 28], [61, 18], [59, 57], [16, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [34, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [51, 57, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1601, 234, 150]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-137, -42, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9605, -2332, 316]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![9605, -2332, 316]] 
 ![![73, 0, 0], ![29, 1, 0], ![3, 0, 1]] where
  M :=![![![9605, -2332, 316], ![-144096, 34765, -4664], ![1135440, -274932, 37097]]]
  hmulB := by decide  
  f := ![![![7394357, -368308, -109292]], ![![3620185, -180319, -53508]], ![![2263191, -112728, -33451]]]
  g := ![![![1045, -2332, 316], ![-15593, 34765, -4664], ![123249, -274932, 37097]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-7394357, 368308, 109292]] ![![9605, -2332, 316]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![117143, -28338, 3818]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![117143, -28338, 3818]] 
 ![![79, 0, 0], ![7, 1, 0], ![51, 0, 1]] where
  M :=![![![117143, -28338, 3818], ![-1741008, 420971, -56676], ![13792632, -3335910, 449309]]]
  hmulB := by decide  
  f := ![![![-80023879, 3985938, 1182790]], ![![-13917967, 693245, 205714]], ![![-71254803, 3549156, 1053179]]]
  g := ![![![1529, -28338, 3818], ![-22751, 420971, -56676], ![180117, -3335910, 449309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5405, 492, 108]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-5405, 492, 108]] 
 ![![79, 0, 0], ![19, 1, 0], ![47, 0, 1]] where
  M :=![![![-5405, 492, 108], ![-49248, 4483, 984], ![-199728, 18180, 3991]]]
  hmulB := by decide  
  f := ![![![2533, -132, -36]], ![![817, -41, -12]], ![![2165, -120, -29]]]
  g := ![![![-251, 492, 108], ![-2287, 4483, 984], ![-9275, 18180, 3991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-959255341, 47779890, 14178238]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-959255341, 47779890, 14178238]] 
 ![![79, 0, 0], ![52, 1, 0], ![44, 0, 1]] where
  M :=![![![-959255341, 47779890, 14178238], ![-6465276528, 322031255, 95559780], ![-18554991576, 924212166, 274251365]]]
  hmulB := by decide  
  f := ![![![-129595, 6342, 4490]], ![![-111220, 7559, 3116]], ![![-95828, -2442, 5805]]]
  g := ![![![-51489267, 47779890, 14178238], ![-347032052, 322031255, 95559780], ![-995963092, 924212166, 274251365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![117143, -28338, 3818]] ![![-5405, 492, 108]]
  ![![-129595, 6342, 4490]] where
 M := ![![![-129595, 6342, 4490]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-129595, 6342, 4490]] ![![-959255341, 47779890, 14178238]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB137I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB137I1 : PrimesBelowBoundCertificateInterval O 31 79 137 where
  m := 11
  g := ![2, 3, 1, 3, 1, 1, 1, 2, 3, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB137I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
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
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N1, I41N0, I41N1, I41N2, I47N0, I47N1, I67N1, I71N0, I71N1, I71N2, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [], [I47N0, I47N0, I47N1], [], [], [], [I67N1], [I71N0, I71N1, I71N2], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
