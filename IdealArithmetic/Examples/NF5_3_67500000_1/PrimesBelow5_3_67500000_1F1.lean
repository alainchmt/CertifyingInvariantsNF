
import IdealArithmetic.Examples.NF5_3_67500000_1.RI5_3_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -1, 5, -3, -2]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-6, -1, 5, -3, -2]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![28, 14, 1, 0, 0], ![7, 18, 0, 1, 0], ![19, 23, 0, 0, 1]] where
  M :=![![![-6, -1, 5, -3, -2], ![-3, -4, -1, 3, -12], ![45, 41, -46, 19, 54], ![-51, -51, 83, -46, -18], ![31, 33, -61, 37, -3]]]
  hmulB := by decide  
  f := ![![![-126, -245, -19, 97, 140]], ![![-129, -274, -19, 113, 162]], ![![-189, -379, -28, 153, 220]], ![![-111, -230, -16, 95, 136]], ![![-182, -372, -27, 151, 217]]]
  g := ![![![-3, 1, 5, -3, -2], ![8, 8, -1, 3, -12], ![6, -31, -46, 19, 54], ![-59, 1, 83, -46, -18], ![53, 10, -61, 37, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [5, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 28], [0, 1]]
 g := ![![[11, 6], [24], [15, 16], [3, 1]], ![[0, 23], [24], [5, 13], [6, 28]]]
 h' := ![![[3, 28], [24, 21], [12, 16], [14, 4], [0, 1]], ![[0, 1], [0, 8], [2, 13], [26, 25], [3, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [5, 26, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144, -144, 457, 276, 536]
  a := ![-5, -7, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-864, -822, 457, 276, 536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![282, 75, -173, 79, 242]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![282, 75, -173, 79, 242]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![27, 6, 1, 0, 0], ![6, 25, 0, 1, 0], ![10, 24, 0, 0, 1]] where
  M :=![![![282, 75, -173, 79, 242], ![-489, -380, 643, -351, -252], ![-297, -143, -434, 485, -1350], ![2997, 2577, -2903, 1144, 3606], ![-2725, -2399, 2923, -1271, -2907]]]
  hmulB := by decide  
  f := ![![![-3978, -7241, 1771, 8679, 10240]], ![![-4683, -6890, 6121, 19339, 21354]], ![![-4881, -8326, 3553, 13768, 15744]], ![![-4938, -7263, 6460, 20405, 22530]], ![![-5161, -8005, 5729, 19015, 21191]]]
  g := ![![![71, -230, -173, 79, 242], ![-456, 365, 643, -351, -252], ![759, 784, -434, 485, -1350], ![1326, -3281, -2903, 1144, 3606], ![-1550, 2814, 2923, -1271, -2907]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [6, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28], [0, 1]]
 g := ![![[28, 5], [25], [21, 1], [6, 1]], ![[0, 24], [25], [27, 28], [12, 28]]]
 h' := ![![[6, 28], [8, 18], [19, 24], [22, 1], [0, 1]], ![[0, 1], [0, 11], [18, 5], [28, 28], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [15, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [6, 23, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5496, 16611, -18799, 65576, 6924]
  a := ![6, -59, -1, -60, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1737, -57799, -18799, 65576, 6924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1043, 3667, 14215, 33354, 34368]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-1043, 3667, 14215, 33354, 34368]] 
 ![![29, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-1043, 3667, 14215, 33354, 34368], ![-3042, 10130, 40063, 94124, 97020], ![-8688, 28333, 112942, 265478, 273684], ![-10788, 34753, 139183, 327255, 337398], ![-531, 1497, 6323, 14915, 15391]]]
  hmulB := by decide  
  f := ![![![-91873, 59799, 6537, -11816, -29016]], ![![-26733, 17395, 1904, -3438, -8448]], ![![-19992, 13043, 1402, -2564, -6300]], ![![-38640, 25125, 2777, -4985, -12198]], ![![-8778, 5726, 606, -1117, -2783]]]
  g := ![![![-21472, 3667, 14215, 33354, 34368], ![-60522, 10130, 40063, 94124, 97020], ![-170625, 28333, 112942, 265478, 273684], ![-210273, 34753, 139183, 327255, 337398], ![-9555, 1497, 6323, 14915, 15391]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-6, -1, 5, -3, -2]] ![![282, 75, -173, 79, 242]]
  ![![-6229, -3718, 1088, 1412, -12954]] where
 M := ![![![-6229, -3718, 1088, 1412, -12954]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-6229, -3718, 1088, 1412, -12954]] ![![-1043, 3667, 14215, 33354, 34368]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![377, 319, -319, 116, 522]]]
 hmul := by decide  
 g := ![![![![13, 11, -11, 4, 18]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -55, 73, -32, -78]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-77, -55, 73, -32, -78]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![21, 15, 18, 1, 0], ![19, 18, 4, 0, 1]] where
  M :=![![![-77, -55, 73, -32, -78], ![138, 134, -225, 128, 42], ![258, 171, 4, -108, 642], ![-1194, -1061, 1269, -543, -1308], ![1035, 943, -1207, 557, 997]]]
  hmulB := by decide  
  f := ![![![79, 151, -31, -166, -198]], ![![96, 144, -111, -362, -402]], ![![120, 105, -338, -906, -966]], ![![171, 230, -285, -847, -924]], ![![118, 186, -128, -429, -479]]]
  g := ![![![67, 59, 31, -32, -78], ![-108, -82, -87, 128, 42], ![-312, -315, -20, -108, 642], ![1131, 988, 525, -543, -1308], ![-955, -818, -491, 557, 997]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [18, 20, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 2, 7], [21, 28, 24], [0, 1]]
 g := ![![[16, 20, 7], [0, 21, 20], [5, 8, 20], [1]], ![[0, 18, 30, 9], [5, 27, 14, 1], [0, 1, 18, 18], [19, 26, 8, 2]], ![[21, 2, 20, 24], [25, 14, 30, 22], [22, 8, 1, 22], [29, 24, 0, 29]]]
 h' := ![![[22, 2, 7], [0, 3, 10], [3, 18, 12], [13, 11, 12], [0, 1]], ![[21, 28, 24], [15, 27, 22], [3, 24, 28], [14, 10, 10], [22, 2, 7]], ![[0, 1], [7, 1, 30], [10, 20, 22], [28, 10, 9], [21, 28, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 24], []]
 b := ![[], [19, 17, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [18, 20, 19, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12983, -13866, 8128, -22311, -30822]
  a := ![-1, -5, 1, -6, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33586, 28245, 17194, -22311, -30822]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-183, 118, 14, -24, -58]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-183, 118, 14, -24, -58]] 
 ![![31, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-183, 118, 14, -24, -58], ![102, -67, -8, 14, 30], ![-48, 46, -5, -4, -6], ![-48, 10, 22, -15, -18], ![50, -18, -18, 14, 15]]]
  hmulB := by decide  
  f := ![![![159, 366, 118, 80, 26]], ![![36, 85, 32, 30, 18]], ![![138, 326, 123, 116, 70]], ![![60, 150, 74, 97, 78]], ![![68, 158, 54, 42, 19]]]
  g := ![![![-5, 118, 14, -24, -58], ![4, -67, -8, 14, 30], ![-2, 46, -5, -4, -6], ![-8, 10, 22, -15, -18], ![8, -18, -18, 14, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2061, -2543, 3903, 11244, 12184]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-2061, -2543, 3903, 11244, 12184]] 
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-2061, -2543, 3903, 11244, 12184], ![-2820, -978, 11521, 29354, 30912], ![-4674, 4027, 33050, 80192, 83388], ![-3384, 9883, 41143, 96967, 100038], ![1039, 2919, 2077, 3473, 3177]]]
  hmulB := by decide  
  f := ![![![-2613, 959, 303, -174, -1784]], ![![-1530, 700, 65, -52, -1012]], ![![-489, -118, 407, -236, -228]], ![![-2178, 465, 311, -77, -1910]], ![![-1799, 1093, 19, -107, -865]]]
  g := ![![![-17002, -2543, 3903, 11244, 12184], ![-47333, -978, 11521, 29354, 30912], ![-132796, 4027, 33050, 80192, 83388], ![-163185, 9883, 41143, 96967, 100038], ![-7180, 2919, 2077, 3473, 3177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-77, -55, 73, -32, -78]] ![![-183, 118, 14, -24, -58]]
  ![![2613, -959, -303, 174, 1784]] where
 M := ![![![2613, -959, -303, 174, 1784]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![2613, -959, -303, 174, 1784]] ![![-2061, -2543, 3903, 11244, 12184]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [33, 23, 27, 33, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 21, 23, 35, 21], [18, 12, 3, 26, 21], [6, 27, 15, 1, 32], [5, 13, 33, 12], [0, 1]]
 g := ![![[5, 22, 32, 36, 36], [34, 33, 30, 16], [16, 21, 0, 12, 1], [], []], ![[4, 32, 2, 2, 11, 7, 7, 34], [28, 34, 28, 12], [10, 17, 29, 19, 22, 3, 22, 27], [20, 17, 18, 1], [9, 36, 28, 34]], ![[7, 25, 10, 24, 33, 34, 15, 4], [4, 16, 2, 34], [30, 22, 13, 35, 34, 30], [18, 4, 35, 9], [9, 31, 20, 34]], ![[0, 20, 27, 24, 0, 3, 30, 22], [17, 24, 25, 21], [27, 32, 24, 13, 8, 29, 13, 31], [11, 27, 4, 27], [14, 27, 31, 25]], ![[6, 20, 23, 30, 32, 0, 12], [21, 34, 21, 27], [12, 35, 3, 1, 36, 15, 36], [29, 20, 28, 26], [4, 33]]]
 h' := ![![[20, 21, 23, 35, 21], [14, 35, 15, 4, 6], [27, 12, 10, 26, 4], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[18, 12, 3, 26, 21], [27, 19, 32, 7, 13], [27, 31, 14, 34, 7], [33, 15, 35, 36, 25], [29, 0, 32, 34, 36], [20, 21, 23, 35, 21]], ![[6, 27, 15, 1, 32], [9, 16, 31, 3, 34], [17, 10, 15, 15, 21], [24, 22, 14, 30], [27, 16, 5, 31, 3], [18, 12, 3, 26, 21]], ![[5, 13, 33, 12], [28, 1, 19, 11, 22], [21, 0, 1, 24, 13], [35, 4, 27, 23, 33], [18, 36, 34, 17, 8], [6, 27, 15, 1, 32]], ![[0, 1], [26, 3, 14, 12, 36], [33, 21, 34, 12, 29], [21, 33, 35, 22, 15], [4, 22, 2, 29, 27], [5, 13, 33, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 20, 26, 13], [], [], []]
 b := ![[], [11, 23, 10, 36, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [33, 23, 27, 33, 25, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5285234105, 19356386682, 116532653919, 199923871227, 260426739573]
  a := ![8, 26, -3, 25, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-142844165, 523145586, 3149531187, 5403347871, 7038560529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![706, -2710, -10184, -23847, -24558]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![706, -2710, -10184, -23847, -24558]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![11, 25, 1, 0, 0], ![6, 1, 0, 1, 0], ![13, 12, 0, 0, 1]] where
  M :=![![![706, -2710, -10184, -23847, -24558], ![2133, -7345, -28690, -67351, -69408], ![6171, -20386, -80867, -190025, -195882], ![7719, -24890, -99646, -234288, -241548], ![408, -1014, -4522, -10700, -11051]]]
  hmulB := by decide  
  f := ![![![392, 78, -186, 71, 384]], ![![-939, -733, 1088, -543, -726]], ![![-454, -409, 569, -281, -366]], ![![132, 73, -76, 19, 180]], ![![-248, -272, 348, -169, -215]]]
  g := ![![![14026, 13913, -10184, -23847, -24558], ![39613, 39272, -28690, -67351, -69408], ![111764, 110778, -80867, -190025, -195882], ![137797, 136564, -99646, -234288, -241548], ![6293, 6228, -4522, -10700, -11051]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [15, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40], [0, 1]]
 g := ![![[19, 8], [31], [31], [30, 4], [1]], ![[35, 33], [31], [31], [38, 37], [1]]]
 h' := ![![[2, 40], [32, 34], [28, 20], [1, 20], [26, 2], [0, 1]], ![[0, 1], [18, 7], [27, 21], [0, 21], [30, 39], [2, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [19, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [15, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2977, -2620, 3176, -1244, -3178]
  a := ![-10, -8, 5, -6, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![265, -1040, 3176, -1244, -3178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -3, -1, 1, 2]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![6, -3, -1, 1, 2]] 
 ![![41, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![6, -3, -1, 1, 2], ![-3, 2, 1, -1, 0], ![-3, -5, 4, -1, -6], ![9, 7, -11, 6, 6], ![-7, -5, 9, -5, -3]]]
  hmulB := by decide  
  f := ![![![42, 77, 11, -19, -32]], ![![3, 6, 1, -1, -2]], ![![39, 72, 11, -16, -28]], ![![3, 6, 2, 1, 0]], ![![23, 42, 6, -10, -17]]]
  g := ![![![0, -3, -1, 1, 2], ![-1, 2, 1, -1, 0], ![0, -5, 4, -1, -6], ![6, 7, -11, 6, 6], ![-6, -5, 9, -5, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2730, -1787, -181, 343, 868]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![2730, -1787, -181, 343, 868]] 
 ![![41, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![2730, -1787, -181, 343, 868], ![-1575, 974, 131, -201, -546], ![1035, -409, -262, 205, 432], ![447, -441, 173, -70, 240], ![-611, 439, -79, 15, -327]]]
  hmulB := by decide  
  f := ![![![9642, -27339, -115201, -271705, -280366]], ![![6513, -18611, -78172, -184336, -190202]], ![![9045, -26210, -109461, -258030, -266216]], ![![4491, -13543, -55657, -131072, -135194]], ![![4789, -13673, -57451, -135477, -139789]]]
  g := ![![![786, -1787, -181, 343, 868], ![-416, 974, 131, -201, -546], ![212, -409, -262, 205, 432], ![49, -441, 173, -70, 240], ![-67, 439, -79, 15, -327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2

def I41N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -1, 15, 38, 40]] i)))

def SI41N3: IdealEqSpanCertificate' Table ![![-3, -1, 15, 38, 40]] 
 ![![41, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-3, -1, 15, 38, 40], ![-6, 6, 43, 104, 108], ![-12, 25, 122, 290, 300], ![-12, 37, 151, 355, 366], ![1, 5, 7, 15, 15]]]
  hmulB := by decide  
  f := ![![![75, -25, -27, 20, 32]], ![![54, -18, -19, 14, 24]], ![![0, -5, 2, 0, -4]], ![![75, -16, -34, 23, 34]], ![![22, -14, -2, 3, 9]]]
  g := ![![![-49, -1, 15, 38, 40], ![-140, 6, 43, 104, 108], ![-396, 25, 122, 290, 300], ![-489, 37, 151, 355, 366], ![-23, 5, 7, 15, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N3 : Nat.card (O ⧸ I41N3) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N3)

lemma isPrimeI41N3 : Ideal.IsPrime I41N3 := prime_ideal_of_norm_prime hp41.out _ NI41N3
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![706, -2710, -10184, -23847, -24558]] ![![6, -3, -1, 1, 2]]
  ![![201, -757, -2857, -6692, -6892]] where
 M := ![![![201, -757, -2857, -6692, -6892]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![201, -757, -2857, -6692, -6892]] ![![2730, -1787, -181, 343, 868]]
  ![![3698, -2408, -262, 475, 1170]] where
 M := ![![![3698, -2408, -262, 475, 1170]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N2 : IdealMulLeCertificate' Table 
  ![![3698, -2408, -262, 475, 1170]] ![![-3, -1, 15, 38, 40]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![1968, -1271, -123, 287, 656]]]
 hmul := by decide  
 g := ![![![![48, -31, -3, 7, 16]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2, I41N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
    exact isPrimeI41N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1 ⊙ MulI41N2)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [22, 28, 32, 40, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 12, 41, 24, 10], [12, 34, 11, 20, 21], [33, 6, 20, 1, 10], [39, 33, 14, 41, 2], [0, 1]]
 g := ![![[24, 37, 39, 27, 1], [31, 18, 14, 9, 35], [4, 20, 10, 24], [1], []], ![[39, 28, 10, 2, 35, 14, 8, 14], [12, 24, 27, 28, 2, 23, 34, 23], [28, 31, 26, 11], [20, 27, 0, 42, 37, 7, 42, 9], [3, 42, 26, 14]], ![[13, 29, 0, 4, 13, 26, 30, 11], [23, 6, 11, 14, 5, 19, 10, 21], [39, 23, 10, 15], [40, 39, 13, 15, 38, 18, 22, 10], [26, 20, 41, 11]], ![[14, 16, 16, 13, 34, 33, 8, 11], [14, 18, 12, 42, 28, 42, 5, 25], [10, 33, 13, 24], [23, 15, 35, 30, 8, 20, 4, 36], [24, 26, 39, 14]], ![[35, 34, 6, 32, 26, 41, 30, 27], [11, 15, 34, 15, 37, 28, 36, 30], [23, 11, 30, 23], [13, 9, 25, 42, 37, 7, 21, 19], [7, 22, 22, 4]]]
 h' := ![![[31, 12, 41, 24, 10], [6, 21, 30, 1, 42], [9, 35, 37, 9, 11], [21, 15, 11, 3, 29], [0, 0, 1], [0, 1]], ![[12, 34, 11, 20, 21], [32, 34, 33, 36, 15], [2, 2, 24, 19, 16], [39, 10, 40, 8, 22], [35, 37, 25, 15, 17], [31, 12, 41, 24, 10]], ![[33, 6, 20, 1, 10], [18, 27, 3, 8, 8], [12, 37, 1, 26, 42], [28, 10, 6, 41, 31], [2, 35, 29, 7, 18], [12, 34, 11, 20, 21]], ![[39, 33, 14, 41, 2], [41, 7, 3, 36, 10], [35, 41, 7, 26, 29], [13, 32, 28, 29, 29], [2, 12, 34, 38, 34], [33, 6, 20, 1, 10]], ![[0, 1], [42, 40, 17, 5, 11], [31, 14, 17, 6, 31], [35, 19, 1, 5, 18], [34, 2, 40, 26, 17], [39, 33, 14, 41, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 20, 9, 5], [], [], []]
 b := ![[], [15, 10, 39, 32, 21], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [22, 28, 32, 40, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![447956102110, 359819422736, -307453659128, 60443461528, 702894657168]
  a := ![6, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10417583770, 8367893552, -7150085096, 1405661896, 16346387376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [8, 5, 0, 29, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 11, 7, 45, 16], [3, 11, 0, 39, 29], [45, 30, 37, 40, 41], [10, 41, 3, 17, 8], [0, 1]]
 g := ![![[25, 42, 12, 0, 2], [42, 33, 28, 32, 37], [27, 46, 3, 10, 1], [1], []], ![[22, 45, 19, 42, 25, 10, 21, 9], [20, 1, 3, 4, 22, 17, 5, 18], [38, 17, 28, 35, 7, 43, 10, 3], [10, 31, 32, 45, 25, 2, 26, 34], [30, 33, 9, 21]], ![[44, 42, 15, 38, 43, 45], [46, 3, 13, 28, 30, 33, 31, 39], [15, 26, 18, 45, 29, 23, 14, 33], [23, 10, 41, 38, 37, 20, 30, 40], [27, 10, 11, 42]], ![[9, 12, 44, 2, 40, 21, 19, 10], [10, 10, 37, 3, 5, 18, 35, 22], [1, 15, 23, 1, 26, 10, 13, 10], [0, 26, 41, 42, 30, 3, 26, 23], [16, 17, 1, 36]], ![[43, 12, 11, 19, 25, 27, 6, 7], [3, 22, 26, 24, 26, 30, 40, 16], [39, 2, 39, 9, 26, 12, 0, 1], [43, 32, 17, 23, 34, 23, 22, 2], [25, 12, 20, 17]]]
 h' := ![![[35, 11, 7, 45, 16], [40, 28, 37, 20, 40], [19, 31, 14, 40, 32], [39, 42, 0, 18, 46], [0, 0, 1], [0, 1]], ![[3, 11, 0, 39, 29], [41, 44, 24, 20, 11], [18, 24, 38, 23, 30], [13, 8, 19, 39, 3], [45, 27, 45, 12, 33], [35, 11, 7, 45, 16]], ![[45, 30, 37, 40, 41], [17, 46, 10, 16], [35, 10, 46, 27, 15], [6, 35, 20, 3, 10], [28, 39, 30, 0, 35], [3, 11, 0, 39, 29]], ![[10, 41, 3, 17, 8], [37, 40, 28, 6, 25], [23, 46, 45, 0, 24], [33, 8, 15, 22, 25], [17, 40, 1, 34, 2], [45, 30, 37, 40, 41]], ![[0, 1], [5, 30, 42, 32, 18], [39, 30, 45, 4, 40], [16, 1, 40, 12, 10], [41, 35, 17, 1, 24], [10, 41, 3, 17, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 34, 21, 29], [], [], []]
 b := ![[], [12, 27, 42, 33, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [8, 5, 0, 29, 1, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1304142135, -851168684, 2029706562, 1592042515, 545029954]
  a := ![6, 6, 4, 7, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27747705, -18109972, 43185246, 33873245, 11596382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4173, 12822, 52304, 123120, 126976]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-4173, 12822, 52304, 123120, 126976]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![49, 13, 50, 1, 0], ![25, 50, 18, 0, 1]] where
  M :=![![![-4173, 12822, 52304, 123120, 126976], ![-11568, 36563, 147510, 346992, 357792], ![-32400, 103542, 415955, 978204, 1008576], ![-39774, 127938, 512676, 1205477, 1242852], ![-1730, 5982, 23330, 54762, 56433]]]
  hmulB := by decide  
  f := ![![![11991, -7830, -836, 1536, 3776]], ![![-6720, 4435, 426, -840, -2112]], ![![3816, -2478, -221, 444, 1296]], ![![13077, -8521, -876, 1637, 4204]], ![![565, -314, -68, 78, 217]]]
  g := ![![![-173801, -149746, -158288, 123120, 126976], ![-489792, -421961, -446082, 346992, 357792], ![-1380732, -1189470, -1257521, 978204, 1008576], ![-1701499, -1465771, -1549670, 1205477, 1242852], ![-77281, -66558, -70388, 54762, 56433]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [18, 33, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 28, 25], [9, 24, 28], [0, 1]]
 g := ![![[28, 33, 15], [25, 10], [46, 34, 10], [20, 6], [1]], ![[17, 52, 47, 52], [4, 40], [52, 11], [16, 13], [26, 8, 51, 43]], ![[48, 18, 16, 11], [28, 37], [45, 2, 46, 15], [39, 9], [49, 10, 35, 10]]]
 h' := ![![[26, 28, 25], [3, 32, 42], [20, 14, 13], [17, 49, 13], [35, 20, 35], [0, 1]], ![[9, 24, 28], [18, 22, 6], [39, 18, 26], [45, 44], [42, 26, 15], [26, 28, 25]], ![[0, 1], [19, 52, 5], [29, 21, 14], [23, 13, 40], [6, 7, 3], [9, 24, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 30], []]
 b := ![[], [34, 14, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [18, 33, 18, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![57869, 45484, -36938, 3431, 93110]
  a := ![2, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-46000, -87823, -35556, 3431, 93110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11991, -7830, -836, 1536, 3776]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![11991, -7830, -836, 1536, 3776]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![11, 6, 1, 0, 0], ![20, 41, 0, 1, 0], ![25, 15, 0, 0, 1]] where
  M :=![![![11991, -7830, -836, 1536, 3776], ![-6720, 4435, 426, -840, -2112], ![3816, -2478, -221, 444, 1296], ![2082, -1698, 48, 217, 444], ![-2518, 1962, -26, -258, -627]]]
  hmulB := by decide  
  f := ![![![-4173, 12822, 52304, 123120, 126976]], ![![-11568, 36563, 147510, 346992, 357792]], ![![-2787, 8754, 35403, 83292, 85888]], ![![-11274, 35537, 143522, 337633, 348148]], ![![-5275, 16509, 66860, 157314, 162221]]]
  g := ![![![-1961, -2310, -836, 1536, 3776], ![1098, 1283, 426, -840, -2112], ![-661, -732, -221, 444, 1296], ![-262, -331, 48, 217, 444], ![351, 417, -26, -258, -627]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [31, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 52], [0, 1]]
 g := ![![[20, 4], [47], [26, 44], [10], [16, 1]], ![[31, 49], [47], [41, 9], [10], [32, 52]]]
 h' := ![![[16, 52], [42, 2], [42, 10], [51, 37], [34, 13], [0, 1]], ![[0, 1], [21, 51], [43, 43], [7, 16], [30, 40], [16, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [21, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [31, 37, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1955, -1660, 1748, -106, -2838]
  a := ![10, 6, 0, 2, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![979, 656, 1748, -106, -2838]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-4173, 12822, 52304, 123120, 126976]] ![![11991, -7830, -836, 1536, 3776]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37457, -49474, -307364, -738718, -766200]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![37457, -49474, -307364, -738718, -766200]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![6, 18, 20, 1, 0], ![46, 43, 56, 0, 1]] where
  M :=![![![37457, -49474, -307364, -738718, -766200], ![82446, -187461, -870638, -2064682, -2133708], ![207078, -581114, -2459221, -5801614, -5986968], ![236808, -754310, -3034076, -7135817, -7357536], ![1530, -53434, -139582, -317274, -323983]]]
  hmulB := by decide  
  f := ![![![199, -130, 1640, -1438, 2736]], ![![-12522, -10683, 10954, -3770, -16836]], ![![39198, 37630, -53651, 27434, 27888]], ![![9582, 9440, -14208, 7587, 5424]], ![![27890, 27627, -41760, 22388, 15365]]]
  g := ![![![673135, 782950, 972444, -738718, -766200], ![1874934, 2181801, 2710350, -2064682, -2133708], ![5261310, 6123518, 7607513, -5801614, -5986968], ![6466074, 7526516, 9350920, -7135817, -7357536], ![284888, 332013, 412694, -317274, -323983]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [49, 21, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 45, 8], [19, 13, 51], [0, 1]]
 g := ![![[36, 39, 48], [39, 34, 41], [4, 35], [20, 2, 35], [1]], ![[35, 23, 30, 50], [56, 48, 15, 23], [40, 3], [50, 6, 8, 14], [48, 45, 23, 40]], ![[51, 21, 43, 48], [54, 51, 6, 29], [56, 57], [31, 56, 1, 36], [32, 13, 21, 19]]]
 h' := ![![[6, 45, 8], [36, 21, 44], [38, 36, 10], [23, 54, 34], [10, 38, 25], [0, 1]], ![[19, 13, 51], [17, 27, 32], [36, 49, 5], [7, 15, 48], [47, 54, 39], [6, 45, 8]], ![[0, 1], [36, 11, 42], [44, 33, 44], [30, 49, 36], [40, 26, 54], [19, 13, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 33], []]
 b := ![[], [49, 13, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [49, 21, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2092, 6508, -17424, 38283, -17452]
  a := ![6, 6, -3, 5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9678, 1150, 3292, 38283, -17452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![128, -68, -34, 33, 24]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![128, -68, -34, 33, 24]] 
 ![![59, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![128, -68, -34, 33, 24], ![27, 121, -62, 7, 126], ![-357, -392, 485, -229, -336], ![147, 164, -440, 306, -246], ![6, -12, 232, -202, 365]]]
  hmulB := by decide  
  f := ![![![12178, -40164, -159420, -374627, -386178]], ![![2445, -8035, -31936, -75054, -77370]], ![![9299, -30556, -121453, -285432, -294240]], ![![3291, -10692, -42682, -100336, -103440]], ![![3398, -11188, -44436, -104426, -107647]]]
  g := ![![![24, -68, -34, 33, 24], ![-14, 121, -62, 7, 126], ![-136, -392, 485, -229, -336], ![289, 164, -440, 306, -246], ![-222, -12, 232, -202, 365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![112, -63, -7, 11, 30]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![112, -63, -7, 11, 30]] 
 ![![59, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![112, -63, -7, 11, 30], ![-57, 48, 5, -11, -24], ![39, -13, -2, 1, 6], ![21, -13, -1, 2, 6], ![-27, 11, 1, -1, -5]]]
  hmulB := by decide  
  f := ![![![8, 3, -17, -31, -24]], ![![1, 0, -3, -7, -6]], ![![3, 1, -8, -13, -12]], ![![5, 2, -10, -17, -12]], ![![5, 1, -13, -27, -23]]]
  g := ![![![-15, -63, -7, 11, 30], ![14, 48, 5, -11, -24], ![-2, -13, -2, 1, 6], ![-3, -13, -1, 2, 6], ![2, 11, 1, -1, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![37457, -49474, -307364, -738718, -766200]] ![![128, -68, -34, 33, 24]]
  ![![-1100, -2094, -170, 811, 1176]] where
 M := ![![![-1100, -2094, -170, 811, 1176]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-1100, -2094, -170, 811, 1176]] ![![112, -63, -7, 11, 30]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-25193, -26609, -2065, 11210, 15222]]]
 hmul := by decide  
 g := ![![![![-427, -451, -35, 190, 258]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3973, 2646, -3084, 1116, 4824]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![3973, 2646, -3084, 1116, 4824]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![26, 29, 42, 28, 1]] where
  M :=![![![3973, 2646, -3084, 1116, 4824], ![-11124, -10235, 14886, -7644, -7776], ![396, 4158, -18275, 14616, -22536], ![61290, 51906, -53784, 18739, 81540], ![-58338, -50922, 58074, -23382, -68837]]]
  hmulB := by decide  
  f := ![![![1993, -7398, -28128, -65916, -67896]], ![![5940, -20195, -79254, -186108, -191808]], ![![17100, -56214, -223403, -525024, -541224]], ![![21330, -68754, -275292, -647273, -667332]], ![![25256, -83065, -330054, -775658, -799589]]]
  g := ![![![-1991, -2250, -3372, -2196, 4824], ![3132, 3529, 5598, 3444, -7776], ![9612, 10782, 15217, 10584, -22536], ![-33750, -37914, -57024, -37121, 81540], ![28384, 31891, 48348, 31214, -68837]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [58, 58, 42, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 24, 17, 17], [23, 34, 51, 12], [9, 2, 54, 32], [0, 1]]
 g := ![![[29, 49, 9, 4], [41, 16, 46], [6, 12, 34, 15], [45, 28, 58, 1], []], ![[38, 14, 4, 15, 8, 28], [4, 10, 52], [15, 14, 52, 41, 25, 32], [35, 50, 33, 51, 37, 40], [15, 3, 54, 1, 0, 33]], ![[27, 1, 15, 16, 39, 12], [22, 40, 45], [31, 8, 12, 56, 23, 4], [44, 18, 22, 17, 56, 14], [45, 14, 35, 27, 12, 20]], ![[16, 33, 24, 49, 41, 44], [21, 57, 42], [31, 55, 60, 36, 14, 29], [32, 33, 58, 50, 39, 51], [49, 28, 29, 28, 57, 11]]]
 h' := ![![[26, 24, 17, 17], [20, 25, 10, 59], [18, 40, 29, 30], [13, 36, 15, 25], [0, 0, 0, 1], [0, 1]], ![[23, 34, 51, 12], [24, 3, 22, 4], [45, 26, 21, 33], [0, 1, 41, 24], [53, 48, 11, 7], [26, 24, 17, 17]], ![[9, 2, 54, 32], [41, 28, 1, 1], [55, 3, 11, 44], [60, 43, 6, 23], [41, 28, 53, 33], [23, 34, 51, 12]], ![[0, 1], [36, 5, 28, 58], [41, 53, 0, 15], [60, 42, 60, 50], [22, 46, 58, 20], [9, 2, 54, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 29, 59], []]
 b := ![[], [], [52, 5, 5, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [58, 58, 42, 3, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![552554, 703376, -241384, 1684612, 1777916]
  a := ![3, 4, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-748742, -833708, -1228096, -788476, 1777916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1993, -7398, -28128, -65916, -67896]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![1993, -7398, -28128, -65916, -67896]] 
 ![![61, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![1993, -7398, -28128, -65916, -67896], ![5940, -20195, -79254, -186108, -191808], ![17100, -56214, -223403, -525024, -541224], ![21330, -68754, -275292, -647273, -667332], ![1098, -2862, -12498, -29538, -30497]]]
  hmulB := by decide  
  f := ![![![3973, 2646, -3084, 1116, 4824]], ![![990, 613, -666, 204, 1296]], ![![2742, 1890, -2423, 1008, 2952]], ![![3610, 2586, -2904, 1039, 4500]], ![![216, -54, 42, -54, 295]]]
  g := ![![![84841, -7398, -28128, -65916, -67896], ![239262, -20195, -79254, -186108, -191808], ![674670, -56214, -223403, -525024, -541224], ![831542, -68754, -275292, -647273, -667332], ![37836, -2862, -12498, -29538, -30497]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![3973, 2646, -3084, 1116, 4824]] ![![1993, -7398, -28128, -65916, -67896]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB402I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB402I1 : PrimesBelowBoundCertificateInterval O 23 61 402 where
  m := 9
  g := ![3, 3, 1, 4, 1, 1, 2, 3, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB402I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2, I41N3]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
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
    · exact ![841, 841, 29]
    · exact ![29791, 31, 31]
    · exact ![69343957]
    · exact ![1681, 41, 41, 41]
    · exact ![147008443]
    · exact ![229345007]
    · exact ![148877, 2809]
    · exact ![205379, 59, 59]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
      exact NI41N3
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
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N2, I31N1, I31N2, I41N1, I41N2, I41N3, I59N1, I59N2, I61N1]
  Il := ![[I29N2], [I31N1, I31N2], [], [I41N1, I41N2, I41N3], [], [], [], [I59N1, I59N2], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
