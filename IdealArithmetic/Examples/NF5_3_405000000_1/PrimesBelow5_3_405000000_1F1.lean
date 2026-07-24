
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![201, -1283, 231, -44, 168]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![201, -1283, 231, -44, 168]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![2, 4, 1, 0, 0], ![21, 15, 0, 1, 0], ![20, 21, 0, 0, 1]] where
  M :=![![![201, -1283, 231, -44, 168], ![88, -559, 97, -17, 72], ![34, -234, 38, -13, 42], ![26, -160, 105, -20, 6], ![36, -184, 33, 13, -5]]]
  hmulB := by decide  
  f := ![![![46999, -120205, 20555, -4612, 15342]], ![![9224, -23593, 4037, -905, 3012]], ![![4576, -11704, 2002, -449, 1494]], ![![38817, -99280, 16979, -3809, 12672]], ![![39500, -101027, 17278, -3876, 12895]]]
  g := ![![![-93, -175, 231, -44, 168], ![-41, -76, 97, -17, 72], ![-21, -37, 38, -13, 42], ![4, -14, 105, -20, 6], ![-7, -14, 33, 13, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [19, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 28], [0, 1]]
 g := ![![[22, 9], [22], [0, 23], [17, 1]], ![[1, 20], [22], [14, 6], [5, 28]]]
 h' := ![![[17, 28], [17, 26], [0, 14], [25, 9], [0, 1]], ![[0, 1], [24, 3], [6, 15], [4, 20], [17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [22, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [19, 12, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![846, -8581, 16043, -3338, 1041]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![622, -1536, 16043, -3338, 1041]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8671, 27564, -4786, 1020, -3550]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-8671, 27564, -4786, 1020, -3550]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![22, 4, 1, 0, 0], ![28, 6, 0, 1, 0], ![5, 1, 0, 0, 1]] where
  M :=![![![-8671, 27564, -4786, 1020, -3550], ![-2040, 7569, -1326, 274, -980], ![-548, 2428, -429, 86, -316], ![-172, 888, -158, 31, -116], ![-2004, 5806, -1002, 218, -745]]]
  hmulB := by decide  
  f := ![![![-3, -48, 98, 12, 34]], ![![-24, -115, 294, 6, 140]], ![![-6, -72, 155, 10, 56]], ![![-8, -114, 234, 31, 84]], ![![-7, -25, 66, 8, 37]]]
  g := ![![![2959, 1522, -4786, 1020, -3550], ![840, 421, -1326, 274, -980], ![278, 136, -429, 86, -316], ![104, 50, -158, 31, -116], ![609, 319, -1002, 218, -745]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [9, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 28], [0, 1]]
 g := ![![[26, 13], [6], [2, 25], [27, 1]], ![[0, 16], [6], [10, 4], [25, 28]]]
 h' := ![![[27, 28], [9, 19], [11, 8], [18, 24], [0, 1]], ![[0, 1], [0, 10], [24, 21], [28, 5], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [20, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [9, 2, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![855, -5963, 14310, -3664, -387]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7222, -1408, 14310, -3664, -387]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 58, -10, 2, -8]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-9, 58, -10, 2, -8]] 
 ![![29, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-9, 58, -10, 2, -8], ![-4, 27, -8, 2, -4], ![-4, 16, -3, -4, 4], ![8, -28, 40, -3, -16], ![4, 4, -16, 14, -17]]]
  hmulB := by decide  
  f := ![![![28555, -73026, 12486, -2802, 9320]], ![![20871, -53375, 9126, -2048, 6812]], ![![22685, -58014, 9919, -2226, 7404]], ![![9854, -25200, 4308, -967, 3216]], ![![21910, -56032, 9580, -2150, 7151]]]
  g := ![![![-29, 58, -10, 2, -8], ![-11, 27, -8, 2, -4], ![-11, 16, -3, -4, 4], ![2, -28, 40, -3, -16], ![18, 4, -16, 14, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![201, -1283, 231, -44, 168]] ![![-8671, 27564, -4786, 1020, -3550]]
  ![![418757, -2673459, 478789, -91396, 350738]] where
 M := ![![![418757, -2673459, 478789, -91396, 350738]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![418757, -2673459, 478789, -91396, 350738]] ![![-9, 58, -10, 2, -8]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![5681651, -36272823, 6496087, -1240040, 4758726]]]
 hmul := by decide  
 g := ![![![![195919, -1250787, 224003, -42760, 164094]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-171, 1253, -162, 33, -184]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-171, 1253, -162, 33, -184]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![23, 22, 12, 1, 1]] where
  M :=![![![-171, 1253, -162, 33, -184], ![-66, 631, -304, 140, -170], ![-280, 894, -479, -244, 500], ![488, -2768, 4662, -991, -464], ![598, -1102, 188, 1018, -1555]]]
  hmulB := by decide  
  f := ![![![-2871, -34583, 74640, 4231, 26858]], ![![-8462, -101841, 219832, 12462, 79102]], ![![-24924, -299946, 647463, 36704, 232976]], ![![-73408, -883420, 1906950, 108103, 686176]], ![![-21641, -260465, 562230, 31872, 202307]]]
  g := ![![![131, 171, 66, 7, -184], ![124, 141, 56, 10, -170], ![-380, -326, -209, -24, 500], ![360, 240, 330, -17, -464], ![1173, 1068, 608, 83, -1555]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [5, 0, 26, 24, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 14, 17, 3], [30, 14, 15, 28], [13, 2, 30], [0, 1]]
 g := ![![[1, 10, 30, 10], [17, 26, 10, 5], [10, 23, 7, 1], []], ![[11, 20, 22, 4, 6, 15], [7, 5, 29, 27, 17, 6], [30, 3, 19, 0, 11, 11], [21, 13, 8, 24, 28, 27]], ![[0, 25, 8, 10, 28, 14], [22, 2, 23, 18, 14, 16], [20, 21, 28, 20, 27, 4], [22, 0, 29, 9, 30, 4]], ![[12, 6, 11, 5, 11], [11, 29, 7, 20, 29], [21, 1, 22, 5, 21], [15, 30, 30]]]
 h' := ![![[26, 14, 17, 3], [8, 14, 3, 14], [12, 9, 15, 25], [0, 0, 0, 1], [0, 1]], ![[30, 14, 15, 28], [13, 24, 12, 25], [28, 15, 2, 8], [18, 24, 12, 13], [26, 14, 17, 3]], ![[13, 2, 30], [7, 20, 0, 4], [10, 22, 16, 6], [13, 11, 11, 3], [30, 14, 15, 28]], ![[0, 1], [10, 4, 16, 19], [25, 16, 29, 23], [14, 27, 8, 14], [13, 2, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 27, 23], []]
 b := ![[], [], [12, 12, 4, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [5, 0, 26, 24, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![121124, 94988, -848496, 666472, -445932]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![334760, 319532, 145248, 35884, -445932]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2871, 34583, -74640, -4231, -26858]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![2871, 34583, -74640, -4231, -26858]] 
 ![![31, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![2871, 34583, -74640, -4231, -26858], ![8462, 101841, -219832, -12462, -79102], ![24924, 299946, -647463, -36704, -232976], ![73408, 883420, -1906950, -108103, -686176], ![46178, 555732, -1199600, -68004, -431651]]]
  hmulB := by decide  
  f := ![![![171, -1253, 162, -33, 184]], ![![129, -950, 130, -29, 142]], ![![169, -1201, 167, -23, 156]], ![![67, -517, -72, 16, 104]], ![![80, -692, 88, -52, 157]]]
  g := ![![![61901, 34583, -74640, -4231, -26858], ![182323, 101841, -219832, -12462, -79102], ![536991, 299946, -647463, -36704, -232976], ![1581581, 883420, -1906950, -108103, -686176], ![994920, 555732, -1199600, -68004, -431651]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-171, 1253, -162, 33, -184]] ![![2871, 34583, -74640, -4231, -26858]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3415, -9092, 1564, -346, 1164]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![3415, -9092, 1564, -346, 1164]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![24, 6, 28, 1, 0], ![19, 3, 22, 0, 1]] where
  M :=![![![3415, -9092, 1564, -346, 1164], ![692, -1933, 346, -72, 252], ![144, -460, 119, -14, 72], ![28, -172, 146, 3, 60], ![844, -2248, 458, -80, 311]]]
  hmulB := by decide  
  f := ![![![-5, 12, -8, -6, 12]], ![![12, -65, 102, -20, -12]], ![![40, 20, -233, 166, -144]], ![![20, 38, -186, 111, -84]], ![![21, 5, -110, 82, -73]]]
  g := ![![![-281, -284, -388, -346, 1164], ![-64, -61, -86, -72, 252], ![-24, -16, -29, -14, 72], ![-32, -10, -34, 3, 60], ![-85, -73, -112, -80, 311]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [10, 14, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 13, 33], [23, 23, 4], [0, 1]]
 g := ![![[15, 10, 26], [12, 21], [11, 14, 30], [21, 1], []], ![[18, 10, 25, 36], [34, 25], [14, 7, 35, 34], [23, 11], [10, 16]], ![[22, 1, 12, 34], [23, 27], [35, 12, 14, 33], [10, 21], [2, 16]]]
 h' := ![![[35, 13, 33], [29, 25, 10], [1, 35, 24], [12, 29, 20], [0, 0, 1], [0, 1]], ![[23, 23, 4], [18, 24, 19], [32, 36, 5], [32, 34, 11], [15, 18, 23], [35, 13, 33]], ![[0, 1], [33, 25, 8], [35, 3, 8], [18, 11, 6], [28, 19, 13], [23, 23, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 36], []]
 b := ![[], [27, 29, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [10, 14, 16, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6140110, -3446923, -20855503, 21191474, -19171295]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3735153, -1975186, -5201305, 21191474, -19171295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 12, -8, -6, 12]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-5, 12, -8, -6, 12]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![6, 9, 1, 0, 0], ![20, 36, 0, 1, 0], ![29, 25, 0, 0, 1]] where
  M :=![![![-5, 12, -8, -6, 12], ![12, -65, 102, -20, -12], ![40, 20, -233, 166, -144], ![-332, 948, -778, -277, 708], ![-44, -288, 902, -444, 275]]]
  hmulB := by decide  
  f := ![![![3415, -9092, 1564, -346, 1164]], ![![692, -1933, 346, -72, 252]], ![![726, -1957, 341, -74, 252]], ![![2520, -6800, 1186, -257, 876]], ![![3167, -8493, 1472, -322, 1091]]]
  g := ![![![-5, 0, -8, -6, 12], ![4, 1, 102, -20, -12], ![62, -7, -233, 166, -144], ![-288, 6, -778, -277, 708], ![-123, 19, 902, -444, 275]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [9, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 36], [0, 1]]
 g := ![![[27, 33], [16], [14, 9], [34], [1]], ![[0, 4], [16], [10, 28], [34], [1]]]
 h' := ![![[16, 36], [7, 25], [22, 4], [34, 34], [28, 16], [0, 1]], ![[0, 1], [0, 12], [12, 33], [23, 3], [25, 21], [16, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [29, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [9, 21, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7899, -45618, 72218, -11104, -6538]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-371, -3578, 72218, -11104, -6538]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![3415, -9092, 1564, -346, 1164]] ![![-5, 12, -8, -6, 12]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [16, 36, 25, 34, 39, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 32, 25, 34, 18], [25, 1, 12, 13, 5], [22, 28, 13, 24, 24], [12, 20, 32, 11, 35], [0, 1]]
 g := ![![[1, 10, 27, 27, 36], [0, 0, 37, 10], [2, 8, 36, 4], [1], []], ![[17, 12, 0, 3, 11, 14, 30, 25], [28, 1, 23, 8], [10, 2, 8, 16], [26, 27, 19, 38, 24, 38, 3, 40], [7, 32, 27, 37]], ![[24, 4, 25, 25, 7, 10, 38, 4], [29, 17, 0, 2], [19, 5, 38, 39], [2, 16, 28, 14, 3, 30, 38, 23], [22, 4, 16, 25]], ![[4, 3, 3, 26, 19, 17, 31, 15], [4, 10], [39, 11, 10, 18], [26, 31, 32, 22, 32, 35, 15, 38], [6, 0, 8, 2]], ![[22, 40, 16, 20, 0, 24, 22, 7], [18, 24, 14, 36], [24, 1, 1, 33], [31, 10, 4, 12, 32, 15, 17, 12], [30, 33, 22, 36]]]
 h' := ![![[25, 32, 25, 34, 18], [33, 14, 2, 14, 35], [19, 9, 34, 30, 16], [25, 5, 16, 7, 2], [0, 0, 1], [0, 1]], ![[25, 1, 12, 13, 5], [36, 9, 2, 36, 21], [22, 30, 14, 21, 7], [31, 24, 22, 3, 37], [21, 16, 23, 1, 5], [25, 32, 25, 34, 18]], ![[22, 28, 13, 24, 24], [20, 4, 32, 34, 3], [22, 30, 6, 17, 24], [30, 31, 27, 28, 11], [27, 14, 20, 39, 12], [25, 1, 12, 13, 5]], ![[12, 20, 32, 11, 35], [23, 35, 8, 20, 4], [28, 39, 20, 16], [23, 4, 20, 11, 10], [19, 32, 12, 30, 13], [22, 28, 13, 24, 24]], ![[0, 1], [24, 20, 38, 19, 19], [5, 15, 8, 39, 35], [26, 18, 38, 33, 22], [33, 20, 26, 12, 11], [12, 20, 32, 11, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 19, 25, 40], [], [], []]
 b := ![[], [32, 9, 16, 7, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [16, 36, 25, 34, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11410563209996, -11373122936268, -24829163427900, 30442519489760, -33617794497660]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![278306419756, -277393242348, -605589351900, 742500475360, -819946207260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8371, 51877, -7261, 1934, -6144]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-8371, 51877, -7261, 1934, -6144]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![22, 5, 32, 1, 0], ![33, 22, 42, 0, 1]] where
  M :=![![![-8371, 51877, -7261, 1934, -6144], ![-3868, 20073, 2383, 1159, -684], ![-2318, 1186, 17394, 1433, 5586], ![-2866, -21796, 55759, 3356, 19770], ![-2416, -9796, 34375, 2245, 11923]]]
  hmulB := by decide  
  f := ![![![117, -331, 133, -38, 42]], ![![76, -127, -67, 125, -144]], ![![-250, 902, -1048, -29, 462]], ![![-116, 437, -604, -71, 366]], ![![-97, 507, -908, 19, 373]]]
  g := ![![![3531, 4125, 4393, 1934, -6144], ![-158, 682, -139, 1159, -684], ![-5074, -2997, -6118, 1433, 5586], ![-16956, -11012, -20511, 3356, 19770], ![-10355, -6589, -12517, 2245, 11923]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [7, 12, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 23, 18], [0, 19, 25], [0, 1]]
 g := ![![[26, 37, 31], [20, 39, 6], [25, 6], [2, 33, 1], []], ![[14, 18, 22, 7], [35, 8, 5, 37], [19, 10], [12, 39, 10, 5], [39, 23]], ![[0, 20, 11, 6], [5, 2, 27, 10], [36, 11], [11, 13, 25, 24], [32, 23]]]
 h' := ![![[33, 23, 18], [32, 14, 17], [21, 4, 7], [29, 3, 7], [0, 0, 1], [0, 1]], ![[0, 19, 25], [4, 41, 16], [17, 37, 33], [35, 14, 15], [42, 29, 19], [33, 23, 18]], ![[0, 1], [8, 31, 10], [1, 2, 3], [9, 26, 21], [34, 14, 23], [0, 19, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 13], []]
 b := ![[], [19, 13, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [7, 12, 10, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12270429, -39766923, 36580486, 13496124, -23769489]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11622066, 9667005, 14023792, 13496124, -23769489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, -224, 40, -8, 30]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![35, -224, 40, -8, 30]] 
 ![![43, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![35, -224, 40, -8, 30], ![16, -101, 22, -4, 12], ![8, -40, -5, 6, 0], ![-12, 20, -22, -17, 36], ![4, -46, 50, -20, 13]]]
  hmulB := by decide  
  f := ![![![1185, -3164, 756, -104, 474]], ![![556, -1493, 370, -48, 228]], ![![826, -2232, 575, -70, 348]], ![![50, -212, 174, 3, 72]], ![![417, -1162, 354, -32, 199]]]
  g := ![![![67, -224, 40, -8, 30], ![28, -101, 22, -4, 12], ![22, -40, -5, 6, 0], ![-6, 20, -22, -17, 36], ![-17, -46, 50, -20, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 82, -10, 2, -12]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-13, 82, -10, 2, -12]] 
 ![![43, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-13, 82, -10, 2, -12], ![-4, 39, -20, 10, -12], ![-20, 64, -39, -16, 36], ![32, -196, 340, -79, -24], ![44, -88, 28, 70, -113]]]
  hmulB := by decide  
  f := ![![![105, 4874, -9254, -494, -3372]], ![![106, 4147, -7944, -426, -2892]], ![![83, 1422, -2921, -162, -1056]], ![![214, 2744, -5864, -331, -2112]], ![![157, 2834, -5786, -320, -2093]]]
  g := ![![![-61, 82, -10, 2, -12], ![-26, 39, -20, 10, -12], ![-55, 64, -39, -16, 36], ![126, -196, 340, -79, -24], ![93, -88, 28, 70, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-8371, 51877, -7261, 1934, -6144]] ![![35, -224, 40, -8, 30]]
  ![![431175, -2752729, 493011, -94104, 361146]] where
 M := ![![![431175, -2752729, 493011, -94104, 361146]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![431175, -2752729, 493011, -94104, 361146]] ![![-13, 82, -10, 2, -12]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![8424517, -53783841, 9632129, -1838680, 7056042]]]
 hmul := by decide  
 g := ![![![![195919, -1250787, 224003, -42760, 164094]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -43, 18, -3, 2]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![15, -43, 18, -3, 2]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![44, 12, 1, 0, 0], ![36, 41, 0, 1, 0], ![18, 26, 0, 0, 1]] where
  M :=![![![15, -43, 18, -3, 2], ![6, 1, -34, 20, -14], ![-40, 102, -65, -46, 92], ![92, -500, 792, -157, -92], ![106, -208, 14, 178, -259]]]
  hmulB := by decide  
  f := ![![![123, -403, -372, -49, -92]], ![![98, 393, -1378, -90, -478]], ![![144, -238, -789, -74, -240]], ![![190, 155, -1750, -131, -582]], ![![108, 138, -1070, -78, -359]]]
  g := ![![![-15, -4, 18, -3, 2], ![22, -1, -34, 20, -14], ![60, 8, -65, -46, 92], ![-584, -25, 792, -157, -92], ![-48, -20, 14, 178, -259]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [13, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 46], [0, 1]]
 g := ![![[45, 4], [7, 7], [29, 18], [27, 18], [1]], ![[8, 43], [1, 40], [27, 29], [25, 29], [1]]]
 h' := ![![[26, 46], [3, 45], [46, 17], [25, 26], [34, 26], [0, 1]], ![[0, 1], [45, 2], [18, 30], [43, 21], [5, 21], [26, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [2, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [13, 21, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![361, -1431, 1658, 5, -604]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1317, -124, 1658, 5, -604]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1447, -3700, 632, -142, 472]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![1447, -3700, 632, -142, 472]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![24, 1, 1, 0, 0], ![23, 23, 0, 1, 0], ![13, 31, 0, 0, 1]] where
  M :=![![![1447, -3700, 632, -142, 472], ![284, -725, 122, -28, 92], ![56, -140, 19, -6, 16], ![12, -20, -14, -1, -4], ![364, -924, 146, -36, 115]]]
  hmulB := by decide  
  f := ![![![-191, 1220, -220, 42, -160]], ![![-84, 533, -94, 16, -68]], ![![-100, 639, -115, 22, -84]], ![![-135, 861, -156, 29, -112]], ![![-109, 693, -124, 22, -89]]]
  g := ![![![-353, -334, 632, -142, 472], ![-68, -65, 122, -28, 92], ![-10, -11, 19, -6, 16], ![9, 3, -14, -1, -4], ![-81, -81, 146, -36, 115]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [31, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 46], [0, 1]]
 g := ![![[46, 7], [22, 9], [36, 28], [45, 21], [1]], ![[28, 40], [19, 38], [11, 19], [38, 26], [1]]]
 h' := ![![[31, 46], [23, 30], [12, 3], [15, 13], [16, 31], [0, 1]], ![[0, 1], [13, 17], [11, 44], [42, 34], [37, 16], [31, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [7, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [31, 16, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10641, -54613, 81154, -8630, -11637]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33772, 9010, 81154, -8630, -11637]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![565, -3641, 696, -121, 492]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![565, -3641, 696, -121, 492]] 
 ![![47, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![565, -3641, 696, -121, 492], ![242, -1645, 424, -46, 258], ![92, -882, 539, 0, 240], ![0, -868, 1278, 59, 480], ![42, -814, 852, 28, 337]]]
  hmulB := by decide  
  f := ![![![11193, -28633, 4910, -1103, 3654]], ![![8144, -20833, 3572, -802, 2658]], ![![4533, -11595, 1985, -447, 1482]], ![![2860, -7324, 1274, -289, 936]], ![![301, -771, 138, -27, 91]]]
  g := ![![![2385, -3641, 696, -121, 492], ![1030, -1645, 424, -46, 258], ![417, -882, 539, 0, 240], ![86, -868, 1278, 59, 480], ![231, -814, 852, 28, 337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![15, -43, 18, -3, 2]] ![![1447, -3700, 632, -142, 472]]
  ![![11193, -28633, 4910, -1103, 3654]] where
 M := ![![![11193, -28633, 4910, -1103, 3654]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![11193, -28633, 4910, -1103, 3654]] ![![565, -3641, 696, -121, 492]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397, -2483, 444, -85, 326]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![397, -2483, 444, -85, 326]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![43, 1, 29, 49, 1]] where
  M :=![![![397, -2483, 444, -85, 326], ![170, -1077, 196, -38, 142], ![76, -474, 87, -12, 56], ![24, -172, -6, -1, 40], ![46, -312, 68, -24, 59]]]
  hmulB := by decide  
  f := ![![![11, -29, 6, -1, 4]], ![![2, -7, 4, 0, 2]], ![![0, -6, 11, 0, 4]], ![![0, -16, 30, 3, 8]], ![![9, -42, 39, 2, 13]]]
  g := ![![![-257, -53, -170, -303, 326], ![-112, -23, -74, -132, 142], ![-44, -10, -29, -52, 56], ![-32, -4, -22, -37, 40], ![-47, -7, -31, -55, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [38, 43, 30, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 49, 34, 30], [8, 24, 30, 17], [30, 32, 42, 6], [0, 1]]
 g := ![![[22, 44, 12, 9], [49, 43, 11], [43, 0, 49, 16], [32, 50, 1], []], ![[19, 8, 36, 6, 47, 5], [31, 3, 10], [38, 6, 9, 14, 32, 34], [38, 10, 17], [1, 46, 23, 48, 41, 23]], ![[35, 4, 32, 15, 13, 10], [34, 44, 29], [2, 31, 42, 5, 27, 24], [0, 33, 25], [30, 22, 52, 38, 35, 37]], ![[20, 13, 11, 1, 29, 16], [23, 22, 13], [35, 9, 43, 13, 18, 24], [18, 15, 24], [13, 28, 2, 51, 19, 4]]]
 h' := ![![[12, 49, 34, 30], [21, 27, 33, 3], [9, 15, 35, 45], [3, 10, 32, 4], [0, 0, 0, 1], [0, 1]], ![[8, 24, 30, 17], [30, 18, 52, 50], [28, 29, 40, 13], [23, 40, 2, 26], [47, 32, 33, 21], [12, 49, 34, 30]], ![[30, 32, 42, 6], [8, 19, 1, 41], [44, 28, 6, 33], [11, 33, 9, 21], [8, 44, 21, 48], [8, 24, 30, 17]], ![[0, 1], [34, 42, 20, 12], [22, 34, 25, 15], [41, 23, 10, 2], [6, 30, 52, 36], [30, 32, 42, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 1, 31], []]
 b := ![[], [], [52, 4, 34, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [38, 43, 30, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3216115988, 10808756918, -11535026719, -976334629, 6150919069]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5051049735, 87883733, -3583239240, -5705120170, 6150919069]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 29, -6, 1, -4]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-11, 29, -6, 1, -4]] 
 ![![53, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-11, 29, -6, 1, -4], ![-2, 7, -4, 0, -2], ![0, 6, -11, 0, -4], ![0, 16, -30, -3, -8], ![-2, 14, -16, -2, -7]]]
  hmulB := by decide  
  f := ![![![-397, 2483, -444, 85, -326]], ![![-168, 1051, -188, 36, -138]], ![![-346, 2164, -387, 74, -284]], ![![-360, 2252, -402, 77, -296]], ![![-293, 1833, -328, 63, -241]]]
  g := ![![![-5, 29, -6, 1, -4], ![2, 7, -4, 0, -2], ![10, 6, -11, 0, -4], ![28, 16, -30, -3, -8], ![15, 14, -16, -2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![397, -2483, 444, -85, 326]] ![![-11, 29, -6, 1, -4]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -3, 44, -17, 16]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-5, -3, 44, -17, 16]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![37, 41, 2, 1, 0], ![39, 36, 27, 0, 1]] where
  M :=![![![-5, -3, 44, -17, 16], ![34, -103, 90, 46, -70], ![-92, 406, -595, 138, 136], ![-276, -360, 2044, -1143, 1100], ![322, -1450, 1982, -116, -449]]]
  hmulB := by decide  
  f := ![![![400699, -1024767, 175226, -39319, 130790]], ![![78638, -201099, 34386, -7716, 25666]], ![![15432, -39458, 6747, -1514, 5036]], ![![306507, -783866, 134034, -30076, 100044]], ![![321621, -822517, 140643, -31559, 104977]]]
  g := ![![![0, 2, -6, -17, 16], ![18, 9, 32, 46, -70], ![-178, -172, -77, 138, 136], ![-15, 117, -430, -1143, 1100], ![375, 330, 243, -116, -449]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [2, 12, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 8, 20], [17, 50, 39], [0, 1]]
 g := ![![[53, 5, 53], [4, 45, 17], [23, 7], [8, 34, 15], [1]], ![[34, 12, 35, 17], [24, 28, 17, 20], [58, 5], [32, 23, 4, 5], [28, 34, 54, 35]], ![[47, 47, 41, 34], [3, 33, 12, 54], [57, 3], [33, 14], [0, 8, 44, 24]]]
 h' := ![![[12, 8, 20], [51, 7, 17], [33, 51, 28], [43, 17, 19], [57, 47, 29], [0, 1]], ![[17, 50, 39], [37, 50, 46], [22, 58, 1], [16, 46, 51], [20, 43, 30], [12, 8, 20]], ![[0, 1], [56, 2, 55], [32, 9, 30], [38, 55, 48], [16, 28], [17, 50, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 39], []]
 b := ![[], [43, 44, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [2, 12, 30, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![935689, -3257833, 3338914, 805086, -1713719]
  a := ![-3, 7, 6, -2, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![643772, 430975, 813545, 805086, -1713719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-400699, 1024767, -175226, 39319, -130790]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-400699, 1024767, -175226, 39319, -130790]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![27, 57, 1, 0, 0], ![54, 23, 0, 1, 0], ![58, 6, 0, 0, 1]] where
  M :=![![![-400699, 1024767, -175226, 39319, -130790], ![-78638, 201099, -34386, 7716, -25666], ![-15432, 39458, -6747, 1514, -5036], ![-3028, 7740, -1324, 297, -988], ![-100746, 257660, -44058, 9886, -32885]]]
  hmulB := by decide  
  f := ![![![5, 3, -44, 17, -16]], ![![-34, 103, -90, -46, 70]], ![![-29, 94, -97, -39, 58]], ![![-4, 49, -110, 17, -6]], ![![-4, 38, -86, 14, -1]]]
  g := ![![![165983, 184628, -175226, 39319, -130790], ![32572, 36231, -34386, 7716, -25666], ![6391, 7109, -6747, 1514, -5036], ![1254, 1395, -1324, 297, -988], ![41734, 46422, -44058, 9886, -32885]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [7, 32, 1] where
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
 g := ![![[13, 17], [49, 12], [3], [0, 19], [27, 1]], ![[0, 42], [19, 47], [3], [41, 40], [54, 58]]]
 h' := ![![[27, 58], [11, 28], [38, 22], [0, 11], [47, 14], [0, 1]], ![[0, 1], [0, 31], [42, 37], [2, 48], [12, 45], [27, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [13, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [7, 32, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15011, -75871, 110093, -7976, -16635]
  a := ![16, -7, -33, 16, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26474, -102846, 110093, -7976, -16635]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-5, -3, 44, -17, 16]] ![![-400699, 1024767, -175226, 39319, -130790]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [50, 3, 17, 14, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 42, 0, 35, 13], [16, 24, 55, 7, 9], [30, 53, 56, 10, 19], [36, 2, 11, 9, 20], [0, 1]]
 g := ![![[2, 38, 40, 51, 48], [33, 15, 49, 48], [18, 21, 35, 37, 41], [5, 43, 1], []], ![[40, 29, 27, 39, 45, 34, 28, 3], [15, 45, 51, 25], [23, 29, 2, 52, 60, 57, 4, 27], [20, 38, 8, 51, 60, 14, 36, 34], [55, 57, 22, 10, 18, 3, 37, 1]], ![[15, 0, 50, 55, 36, 20, 45, 52], [36, 15, 14, 27], [19, 45, 9, 29, 21, 30, 57, 34], [55, 46, 60, 37, 24, 49], [49, 50, 48, 15, 11, 37, 47, 58]], ![[22, 34, 24, 21, 54, 19, 30, 15], [36, 10, 22, 48], [34, 1, 11, 54, 47, 45, 11, 4], [37, 40, 25, 16, 35, 43, 26, 4], [20, 5, 15, 3, 43, 9, 35, 27]], ![[59, 16, 55, 27, 33, 43, 47, 19], [50, 19, 7, 56], [27, 2, 54, 55, 4, 48, 10, 34], [19, 60, 31, 0, 54, 18, 23, 41], [30, 56, 18, 19, 31, 56, 24, 9]]]
 h' := ![![[22, 42, 0, 35, 13], [39, 51, 35, 0, 32], [15, 30, 10, 40, 32], [55, 31, 41, 50, 23], [0, 0, 0, 1], [0, 1]], ![[16, 24, 55, 7, 9], [21, 44, 27, 20, 18], [10, 59, 17, 44, 5], [56, 22, 50, 56, 54], [29, 19, 26, 54, 45], [22, 42, 0, 35, 13]], ![[30, 53, 56, 10, 19], [8, 53, 15, 13, 11], [10, 12, 37, 15, 37], [11, 20, 42, 21, 27], [60, 47, 15, 18], [16, 24, 55, 7, 9]], ![[36, 2, 11, 9, 20], [30, 2, 24, 3, 59], [0, 34, 22, 30, 29], [4, 13, 4, 23, 27], [14, 50, 0, 5, 27], [30, 53, 56, 10, 19]], ![[0, 1], [2, 33, 21, 25, 2], [1, 48, 36, 54, 19], [31, 36, 46, 33, 52], [16, 6, 20, 44, 50], [36, 2, 11, 9, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 59, 11, 50], [], [], []]
 b := ![[], [27, 23, 43, 2, 29], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [50, 3, 17, 14, 18, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![343742384477, 2766541499618, -8270241487056, 3904747964920, -2377163595854]
  a := ![7, -3, -13, 6, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5635121057, 45353139338, -135577729296, 64012261720, -38969895014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB984I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB984I1 : PrimesBelowBoundCertificateInterval O 23 61 984 where
  m := 9
  g := ![3, 2, 2, 1, 3, 3, 2, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB984I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
    · exact ![923521, 31]
    · exact ![50653, 1369]
    · exact ![115856201]
    · exact ![79507, 43, 43]
    · exact ![2209, 2209, 47]
    · exact ![7890481, 53]
    · exact ![205379, 3481]
    · exact ![844596301]
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
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
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
  β := ![I29N0, I29N1, I29N2, I31N1, I43N1, I43N2, I47N2, I53N1]
  Il := ![[I29N0, I29N1, I29N2], [I31N1], [], [], [I43N1, I43N2], [I47N2], [I53N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
