
import IdealArithmetic.Examples.NF5_1_25000000_1.RI5_1_25000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 2, 5, 0, 11]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-10, 2, 5, 0, 11]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-10, 2, 5, 0, 11], ![-44, -5, 12, -2, 33], ![-128, -28, 27, -8, 85], ![-6, -6, -2, -1, -1], ![-92, -22, 18, -6, 59]]]
  hmulB := by decide  
  f := ![![![3, -2, -1, 0, 2]], ![![-4, 1, -2, -4, 3]], ![![-4, 2, 13, 6, -19]], ![![19, -2, -5, 13, 5]], ![![4, -2, -6, -2, 9]]]
  g := ![![![-5, 2, 5, 0, 11], ![-22, -5, 12, -2, 33], ![-64, -28, 27, -8, 85], ![-3, -6, -2, -1, -1], ![-46, -22, 18, -6, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 3, -1, 1, -5]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![9, 3, -1, 1, -5]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![9, 3, -1, 1, -5], ![18, 6, -3, 1, -8], ![30, 13, -4, -1, -17], ![-2, -1, 5, 6, -4], ![24, 8, -2, 4, -12]]]
  hmulB := by decide  
  f := ![![![-178, 204, 6, 56, -89]], ![![33, -40, -1, -11, 18]], ![![-261, 298, 9, 82, -130]], ![![25, -29, -1, -8, 13]], ![![-30, 33, 1, 9, -14]]]
  g := ![![![3, 3, -1, 1, -5], ![7, 6, -3, 1, -8], ![11, 13, -4, -1, -17], ![-6, -1, 5, 6, -4], ![7, 8, -2, 4, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2275, -2634, -75, -723, 1157]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2275, -2634, -75, -723, 1157]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2275, -2634, -75, -723, 1157], ![-3182, 3646, 108, 1001, -1590], ![4358, -5076, -142, -1393, 2237], ![-2924, 3377, 97, 927, -1481], ![724, -868, -22, -238, 389]]]
  hmulB := by decide  
  f := ![![![-18, 7, 21, 2, -31]], ![![51, 3, 31, 69, -55]], ![![13, -52, -221, -178, 342]], ![![-294, 65, 160, -114, -214]], ![![-28, 29, 111, 70, -170]]]
  g := ![![![2492, -2634, -75, -723, 1157], ![-3468, 3646, 108, 1001, -1590], ![4788, -5076, -142, -1393, 2237], ![-3199, 3377, 97, 927, -1481], ![807, -868, -22, -238, 389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-10, 2, 5, 0, 11]] ![![9, 3, -1, 1, -5]]
  ![![360, 135, -38, 31, -183]] where
 M := ![![![360, 135, -38, 31, -183]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![360, 135, -38, 31, -183]] ![![9, 3, -1, 1, -5]]
  ![![76, -99, -92, -13, -162]] where
 M := ![![![76, -99, -92, -13, -162]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![76, -99, -92, -13, -162]] ![![2275, -2634, -75, -723, 1157]]
  ![![7706, 2569, -1025, 614, -4227]] where
 M := ![![![7706, 2569, -1025, 614, -4227]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![7706, 2569, -1025, 614, -4227]] ![![2275, -2634, -75, -723, 1157]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![33958, 14384, -2396, 3160, -15430]]]
 hmul := by decide  
 g := ![![![![16979, 7192, -1198, 1580, -7715]]]]
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


def P3P0 : CertificateIrreducibleZModOfList' 3 5 2 1 [1, 1, 0, 1, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 1], [0, 0, 1, 1, 2], [2, 2, 0, 2, 2], [1, 0, 2, 2, 2], [0, 1]]
 g := ![![[]], ![[0, 0, 2, 0, 1]], ![[1, 0, 0, 0, 1, 1, 0, 2]], ![[1, 2, 2, 0, 2, 1, 0, 2]], ![[1, 1, 2, 0, 2, 1, 0, 2]]]
 h' := ![![[0, 0, 0, 1], [0, 1]], ![[0, 0, 1, 1, 2], [0, 0, 0, 1]], ![[2, 2, 0, 2, 2], [0, 0, 1, 1, 2]], ![[1, 0, 2, 2, 2], [2, 2, 0, 2, 2]], ![[0, 1], [1, 0, 2, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], [], [], []]
 b := ![[], [1, 0, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 5
  hpos := by decide
  P := [1, 1, 0, 1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23086755683565, -3537798992793, -24461477334531, -40447863187962, 40882147104771]
  a := ![26, 17, 31, 30, -91]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7695585227855, -1179266330931, -8153825778177, -13482621062654, 13627382368257]
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


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -3, 1, 4, -1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![7, -3, 1, 4, -1]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![7, -3, 1, 4, -1], ![-4, 0, -17, -14, 25], ![-72, 7, 22, -48, -23], ![84, 8, 54, 121, -96], ![40, -6, -6, 28, 5]]]
  hmulB := by decide  
  f := ![![![-1137, -401, 137, -94, 603]], ![![-1127, -403, 132, -94, 592]], ![![-1073, -400, 115, -92, 548]], ![![-539, -193, 63, -45, 283]], ![![-986, -364, 108, -84, 507]]]
  g := ![![![1, -3, 1, 4, -1], ![1, 0, -17, -14, 25], ![15, 7, 22, -48, -23], ![-33, 8, 54, 121, -96], ![-6, -6, -6, 28, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![7, -3, 1, 4, -1]] ![![7, -3, 1, 4, -1]]
  ![![285, 24, 302, 478, -494]] where
 M := ![![![285, 24, 302, 478, -494]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![285, 24, 302, 478, -494]] ![![7, -3, 1, 4, -1]]
  ![![547, 8047, 35297, 30314, -54989]] where
 M := ![![![547, 8047, 35297, 30314, -54989]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![547, 8047, 35297, 30314, -54989]] ![![7, -3, 1, 4, -1]]
  ![![-2222927, 817884, 2607172, 323576, -3796292]] where
 M := ![![![-2222927, 817884, 2607172, 323576, -3796292]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-2222927, 817884, 2607172, 323576, -3796292]] ![![7, -3, 1, 4, -1]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-331219705, 50285345, 81481685, -212629820, -87339685]]]
 hmul := by decide  
 g := ![![![![-66243941, 10057069, 16296337, -42525964, -17467937]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235, -23, -193, -364, 329]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-235, -23, -193, -364, 329]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![1, 4, 1, 0, 0], ![2, 5, 0, 1, 0], ![4, 2, 0, 0, 1]] where
  M :=![![![-235, -23, -193, -364, 329], ![-588, 300, 1047, 390, -1561], ![5464, -321, 834, 5360, -1953], ![-3312, -1020, -5702, -7667, 9282], ![-2592, 70, -746, -2840, 1473]]]
  hmulB := by decide  
  f := ![![![-23185, 26929, 765, 7390, -11837]], ![![32568, -37200, -1101, -10216, 16219]], ![![8949, -9996, -311, -2748, 4312]], ![![20898, -23808, -709, -6539, 10367]], ![![-4996, 6030, 156, 1652, -2697]]]
  g := ![![![-90, 273, -193, -364, 329], ![547, -388, 1047, 390, -1561], ![246, -3793, 834, 5360, -1953], ![-2772, 5937, -5702, -7667, 9282], ![-294, 2044, -746, -2840, 1473]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[2, 2], [4, 1]], ![[3, 5], [1, 6]]]
 h' := ![![[4, 6], [1, 4], [0, 1]], ![[0, 1], [3, 3], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2312649, -827989, -2915517, -3902226, 5414867]
  a := ![239, 117, 236, 172, -835]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1893164, 2787925, -2915517, -3902226, 5414867]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-929, 1071, 31, 294, -469]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-929, 1071, 31, 294, -469]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-929, 1071, 31, 294, -469], ![1288, -1486, -43, -408, 651], ![-1788, 2061, 60, 566, -903], ![1192, -1374, -40, -377, 602], ![-304, 350, 10, 96, -153]]]
  hmulB := by decide  
  f := ![![![53, 11, -11, 4, -35]], ![![34, 8, -7, 2, -21]], ![![65, 18, -11, 4, -42]], ![![0, 0, 2, 3, 0]], ![![46, 12, -8, 4, -27]]]
  g := ![![![-318, 1071, 31, 294, -469], ![441, -1486, -43, -408, 651], ![-612, 2061, 60, 566, -903], ![408, -1374, -40, -377, 602], ![-104, 350, 10, 96, -153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -4, -14, -6, 21]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, -4, -14, -6, 21]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, -4, -14, -6, 21], ![-72, 5, -8, -68, 21], ![52, 56, 261, 266, -413], ![272, -84, -250, 19, 357], ![-4, -30, -130, -114, 203]]]
  hmulB := by decide  
  f := ![![![-139, -90, 4, -20, 67]], ![![-112, -65, 2, -14, 47]], ![![-129, -92, -1, -20, 56]], ![![-22, -14, 0, -3, 9]], ![![-100, -94, -22, -18, 7]]]
  g := ![![![15, -4, -14, -6, 3], ![12, 5, -8, -68, 3], ![-287, 56, 261, 266, -59], ![260, -84, -250, 19, 51], ![142, -30, -130, -114, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P2 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[5, 2], [1, 1]], ![[0, 5], [2, 6]]]
 h' := ![![[1, 6], [3, 4], [0, 1]], ![[0, 1], [0, 3], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [6, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N2 : CertifiedPrimeIdeal' SI7N2 7 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P7P2
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17473, -3752, -16022, -26064, 29568]
  a := ![19, 11, 21, 18, -66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18539, -3752, -16022, -26064, 4224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N2 B_one_repr
lemma NI7N2 : Nat.card (O ⧸ I7N2) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-235, -23, -193, -364, 329]] ![![-929, 1071, 31, 294, -469]]
  ![![-129, 6, -26, -132, 56]] where
 M := ![![![-129, 6, -26, -132, 56]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-129, 6, -26, -132, 56]] ![![7, -4, -14, -6, 21]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-38815, 8498, 20692, -15442, -27601]]]
 hmul := by decide  
 g := ![![![![-5545, 1214, 2956, -2206, -3943]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![751, -867, -25, -238, 380]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![751, -867, -25, -238, 380]] 
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![751, -867, -25, -238, 380], ![-1044, 1202, 35, 330, -526], ![1444, -1669, -48, -458, 732], ![-964, 1112, 32, 305, -487], ![244, -284, -8, -78, 125]]]
  hmulB := by decide  
  f := ![![![61, 23, -5, 6, -36]], ![![12, 4, -1, 2, -6]], ![![20, 7, -6, -2, -4]], ![![-8, 0, 4, -1, -3]], ![![46, 18, -2, 6, -29]]]
  g := ![![![-139, -867, -25, -238, 380], ![192, 1202, 35, 330, -526], ![-268, -1669, -48, -458, 732], ![178, 1112, 32, 305, -487], ![-46, -284, -8, -78, 125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, -8, -6, 12]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![1, -2, -8, -6, 12]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![1, -2, -8, -6, 12], ![-36, 5, 6, -26, -6], ![76, 22, 121, 166, -200], ![88, -46, -162, -63, 242], ![-24, -12, -64, -76, 101]]]
  hmulB := by decide  
  f := ![![![-7421, 8530, 248, 2342, -3732]], ![![-418, 473, 14, 130, -206]], ![![-6021, 6920, 201, 1900, -3028]], ![![-5207, 5984, 174, 1643, -2618]], ![![-3595, 4130, 120, 1134, -1807]]]
  g := ![![![5, -2, -8, -6, 12], ![16, 5, 6, -26, -6], ![-119, 22, 121, 166, -200], ![61, -46, -162, -63, 242], ![57, -12, -64, -76, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -29, -1, -8, 13]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![25, -29, -1, -8, 13]] 
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![25, -29, -1, -8, 13], ![-36, 40, 1, 10, -17], ![48, -55, 2, -12, 19], ![-28, 36, -2, 11, -12], ![8, -10, -2, -4, 7]]]
  hmulB := by decide  
  f := ![![![191, 55, -31, 14, -113]], ![![108, 32, -17, 8, -63]], ![![186, 57, -28, 14, -107]], ![![9, 3, -1, 1, -5]], ![![158, 48, -24, 12, -91]]]
  g := ![![![7, -29, -1, -8, 13], ![-10, 40, 1, 10, -17], ![14, -55, 2, -12, 19], ![-9, 36, -2, 11, -12], ![2, -10, -2, -4, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2

def I11N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 1, 2, -3]] i)))

def SI11N3: IdealEqSpanCertificate' Table ![![3, 1, 1, 2, -3]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![3, 1, 1, 2, -3], ![8, 0, -5, 0, 5], ![-20, 3, -10, -30, 15], ![8, 6, 32, 35, -50], ![16, 2, 6, 16, -13]]]
  hmulB := by decide  
  f := ![![![-395, 437, 15, 120, -185]], ![![-170, 182, 7, 50, -75]], ![![-360, 393, 14, 108, -165]], ![![-314, 346, 12, 95, -146]], ![![-123, 131, 5, 36, -54]]]
  g := ![![![-2, 1, 1, 2, -3], ![3, 0, -5, 0, 5], ![27, 3, -10, -30, 15], ![-44, 6, 32, 35, -50], ![-15, 2, 6, 16, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N3 : Nat.card (O ⧸ I11N3) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N3)

lemma isPrimeI11N3 : Ideal.IsPrime I11N3 := prime_ideal_of_norm_prime hp11.out _ NI11N3

def I11N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -3, -9, 0, 13]] i)))

def SI11N4: IdealEqSpanCertificate' Table ![![9, -3, -9, 0, 13]] 
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![9, -3, -9, 0, 13], ![-52, 0, -21, -62, 39], ![-32, 51, 206, 148, -317], ![272, -56, -130, 121, 170], ![32, -26, -98, -56, 149]]]
  hmulB := by decide  
  f := ![![![551, 161, -47, 34, -229]], ![![578, 186, -49, 40, -249]], ![![646, 199, -52, 42, -267]], ![![262, 80, -22, 17, -110]], ![![284, 94, -22, 20, -119]]]
  g := ![![![7, -3, -9, 0, 13], ![34, 0, -21, -62, 39], ![-202, 51, 206, 148, -317], ![66, -56, -130, 121, 170], ![92, -26, -98, -56, 149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N4 : Nat.card (O ⧸ I11N4) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N4)

lemma isPrimeI11N4 : Ideal.IsPrime I11N4 := prime_ideal_of_norm_prime hp11.out _ NI11N4
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![751, -867, -25, -238, 380]] ![![1, -2, -8, -6, 12]]
  ![![-1, 1, 1, 0, -2]] where
 M := ![![![-1, 1, 1, 0, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-1, 1, 1, 0, -2]] ![![25, -29, -1, -8, 13]]
  ![![-29, 34, 8, 14, -25]] where
 M := ![![![-29, 34, 8, 14, -25]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N2 : IdealMulLeCertificate' Table 
  ![![-29, 34, 8, 14, -25]] ![![3, 1, 1, 2, -3]]
  ![![-263, 29, 19, -208, 2]] where
 M := ![![![-263, 29, 19, -208, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N3 : IdealMulLeCertificate' Table 
  ![![-263, 29, 19, -208, 2]] ![![9, -3, -9, 0, 13]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-60995, 13354, 32516, -24266, -43373]]]
 hmul := by decide  
 g := ![![![![-5545, 1214, 2956, -2206, -3943]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2, I11N3, I11N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
    exact isPrimeI11N3
    exact isPrimeI11N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1 ⊙ MulI11N2 ⊙ MulI11N3)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -1, 1, 0, -1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-3, -1, 1, 0, -1]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![4, 1, 1, 0, 0], ![10, 7, 0, 1, 0], ![7, 2, 0, 0, 1]] where
  M :=![![![-3, -1, 1, 0, -1], ![4, -2, 1, 6, -3], ![0, -7, -24, -20, 33], ![-24, 8, 18, -7, -26], ![0, 2, 10, 8, -19]]]
  hmulB := by decide  
  f := ![![![-275, 313, 9, 86, -137]], ![![376, -438, -13, -120, 191]], ![![-96, 109, 3, 30, -48]], ![![18, -26, -1, -7, 11]], ![![-97, 109, 3, 30, -48]]]
  g := ![![![0, 0, 1, 0, -1], ![-3, -3, 1, 6, -3], ![5, 7, -24, -20, 33], ![12, 7, 18, -7, -26], ![1, -2, 10, 8, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12], [0, 1]]
 g := ![![[1, 1], [10], [8, 1]], ![[9, 12], [10], [3, 12]]]
 h' := ![![[8, 12], [3, 1], [12, 7], [0, 1]], ![[0, 1], [11, 12], [3, 6], [8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [12, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-576815, -121658, -509160, -838654, 954621]
  a := ![-107, -61, -118, -103, 375]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![243386, 334526, -509160, -838654, 954621]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18189, 20899, 609, 5738, -9140]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-18189, 20899, 609, 5738, -9140]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![9, 11, 1, 0, 0], ![0, 9, 0, 1, 0], ![10, 2, 0, 0, 1]] where
  M :=![![![-18189, 20899, 609, 5738, -9140], ![25084, -29056, -835, -7974, 12746], ![-35036, 40197, 1170, 11038, -17580], ![23308, -26820, -780, -7363, 11735], ![-6004, 6804, 200, 1870, -2967]]]
  hmulB := by decide  
  f := ![![![-185, 79, 263, 66, -388]], ![![1420, -54, 341, 1498, -702]], ![![1059, -86, 58, 950, -218]], ![![500, 86, 569, 909, -947]], ![![50, 102, 456, 430, -717]]]
  g := ![![![5210, -1474, 609, 5738, -9140], ![-7297, 2031, -835, -7974, 12746], ![10018, -2835, 1170, 11038, -17580], ![-6694, 1889, -780, -7363, 11735], ![1682, -484, 200, 1870, -2967]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[5, 4], [9], [9, 1]], ![[2, 9], [9], [5, 12]]]
 h' := ![![[9, 12], [2, 2], [11, 10], [0, 1]], ![[0, 1], [7, 11], [10, 3], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [7, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94409, 2662, -18682, -93850, 42898]
  a := ![35, 28, 52, 60, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27327, 74386, -18682, -93850, 42898]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -2, -4, 6, 5]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![11, -2, -4, 6, 5]] 
 ![![13, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![11, -2, -4, 6, 5], ![-32, -5, -34, -56, 57], ![-116, 46, 151, 30, -221], ![272, -28, -10, 223, -17], ![68, -22, -66, 2, 95]]]
  hmulB := by decide  
  f := ![![![451, -248, -22, -72, 61]], ![![27, 25, -2, 6, -20]], ![![492, -260, -23, -76, 63]], ![![205, -106, -10, -31, 24]], ![![339, -170, -16, -50, 38]]]
  g := ![![![-2, -2, -4, 6, 5], ![20, -5, -34, -56, 57], ![-15, 46, 151, 30, -221], ![-76, -28, -10, 223, -17], ![1, -22, -66, 2, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-3, -1, 1, 0, -1]] ![![-18189, 20899, 609, 5738, -9140]]
  ![![451, -248, -22, -72, 61]] where
 M := ![![![451, -248, -22, -72, 61]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![451, -248, -22, -72, 61]] ![![11, -2, -4, 6, 5]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [1, 12, 6, 13, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12, 4, 4, 9], [2, 8, 14, 5, 10], [1, 6, 10, 10, 1], [14, 7, 6, 15, 14], [0, 1]]
 g := ![![[10, 8, 12, 12, 4], [2, 2, 7, 1], [], []], ![[3, 6, 3, 5, 10, 7, 16, 9], [8, 7, 0, 16], [10, 16, 1, 13], [14, 6, 10, 13]], ![[14, 9, 16, 6, 5, 10, 10, 3], [2, 0, 4, 4], [6, 14, 15, 13], [13, 15, 1, 15]], ![[2, 13, 5, 5, 10, 14, 5, 9], [5, 7, 16, 13], [7, 1, 5, 1], [6, 7, 10, 1]], ![[11, 9, 16, 4, 4, 16, 0, 11], [4, 16, 9, 15], [11, 16, 11, 1], [7, 2, 7, 9]]]
 h' := ![![[7, 12, 4, 4, 9], [15, 8, 8, 13, 2], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[2, 8, 14, 5, 10], [5, 11, 8, 0, 1], [8, 5, 4, 14, 13], [1, 11, 0, 5, 8], [7, 12, 4, 4, 9]], ![[1, 6, 10, 10, 1], [13, 4, 14, 13, 6], [7, 2, 14, 11, 2], [8, 14, 14, 9, 9], [2, 8, 14, 5, 10]], ![[14, 7, 6, 15, 14], [13, 15, 8, 2, 14], [1, 7, 2, 7, 8], [12, 1, 11, 1, 16], [1, 6, 10, 10, 1]], ![[0, 1], [11, 13, 13, 6, 11], [10, 3, 14, 2, 10], [2, 8, 8, 2, 1], [14, 7, 6, 15, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 5, 1, 13], [], [], []]
 b := ![[], [16, 9, 0, 14, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [1, 12, 6, 13, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-163688253363887, -23138682204808, -165100792425856, -279691238044440, 276872867702200]
  a := ![-28, -30, -56, -78, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9628720786111, -1361098953224, -9711811319168, -16452425767320, 16286639276600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [9, 7, 3, 8, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9, 8, 0, 9], [17, 11, 2, 15, 13], [16, 17, 15, 16, 2], [14, 0, 13, 7, 14], [0, 1]]
 g := ![![[14, 10, 2, 17, 11], [16, 18, 1, 16, 1], [], []], ![[1, 8, 15, 11, 9, 2, 18, 9], [7, 14, 0, 3, 5, 8, 13, 7], [3, 3, 9, 16], [10, 16, 4, 5]], ![[10, 5, 13, 12, 10, 6, 5, 12], [2, 18, 16, 2, 11, 6, 6, 10], [2, 9, 18, 7], [2, 17, 16, 17]], ![[18, 6, 9, 3, 9, 13, 9, 8], [11, 6, 15, 14, 0, 4, 17, 14], [3, 6, 9, 1], [2, 14, 14, 4]], ![[10, 8, 0, 5, 0, 17, 5, 13], [17, 12, 5, 8, 12, 7, 9, 13], [0, 18, 7, 6], [7, 2, 7, 6]]]
 h' := ![![[7, 9, 8, 0, 9], [8, 11, 7, 9, 7], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[17, 11, 2, 15, 13], [1, 18, 2, 7, 18], [1, 5, 0, 8, 10], [16, 7, 15, 0, 4], [7, 9, 8, 0, 9]], ![[16, 17, 15, 16, 2], [17, 11, 17, 13, 6], [7, 18, 18, 9, 7], [5, 17, 15, 13, 11], [17, 11, 2, 15, 13]], ![[14, 0, 13, 7, 14], [7, 16, 8, 11, 17], [16, 6, 14, 7, 11], [10, 5, 7, 13, 18], [16, 17, 15, 16, 2]], ![[0, 1], [18, 1, 4, 17, 9], [0, 9, 6, 14, 9], [0, 9, 0, 12, 5], [14, 0, 13, 7, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 6, 13, 18], [], [], []]
 b := ![[], [4, 7, 4, 1, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [9, 7, 3, 8, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54386362874187, -6429746488214, -5551689254472, 41568769037270, 2144624519851]
  a := ![17, 23, 43, 61, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2862440151273, -338407709906, -292194171288, 2187829949330, 112874974729]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 20, 6, 4, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![21, 20, 6, 4, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![11, 15, 1, 0, 0], ![5, 14, 0, 1, 0], ![4, 12, 0, 0, 1]] where
  M :=![![![21, 20, 6, 4, 1], ![-12, 19, 16, 2, 31], ![-128, 0, 43, -8, 107], ![-36, -22, 4, 3, 5], ![-100, -10, 30, -2, 79]]]
  hmulB := by decide  
  f := ![![![-3241, 3738, 108, 1026, -1637]], ![![4496, -5185, -150, -1424, 2271]], ![![1111, -1281, -37, -352, 561]], ![![2213, -2552, -74, -701, 1118]], ![![1736, -2002, -58, -550, 877]]]
  g := ![![![-3, -6, 6, 4, 1], ![-14, -27, 16, 2, 31], ![-43, -79, 43, -8, 107], ![-5, -8, 4, 3, 5], ![-32, -60, 30, -2, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [8, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22], [0, 1]]
 g := ![![[7, 3], [20, 2], [11, 8], [1]], ![[0, 20], [0, 21], [0, 15], [1]]]
 h' := ![![[13, 22], [1, 7], [4, 5], [15, 13], [0, 1]], ![[0, 1], [0, 16], [0, 18], [0, 10], [13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [10, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [8, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![465, 253, 2750, 3047, -3872]
  a := ![-1, -5, -8, -15, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1284, -1617, 2750, 3047, -3872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5039, -5807, -169, -1594, 2541]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![5039, -5807, -169, -1594, 2541]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![13, 18, 1, 0, 0], ![4, 17, 0, 1, 0], ![8, 2, 0, 0, 1]] where
  M :=![![![5039, -5807, -169, -1594, 2541], ![-6976, 8058, 231, 2212, -3535], ![9716, -11169, -328, -3066, 4879], ![-6460, 7450, 216, 2045, -3262], ![1664, -1894, -58, -520, 821]]]
  hmulB := by decide  
  f := ![![![29, -3, 13, 40, -21]], ![![4, -38, -137, -106, 217]], ![![-9, -28, -95, -80, 154]], ![![36, -26, -77, -29, 119]], ![![24, -6, -8, 16, 11]]]
  g := ![![![-292, 837, -169, -1594, 2541], ![411, -1158, 231, 2212, -3535], ![-556, 1613, -328, -3066, 4879], ![376, -1073, 216, 2045, -3262], ![-90, 276, -58, -520, 821]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [4, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22], [0, 1]]
 g := ![![[14, 6], [16, 3], [0, 8], [1]], ![[0, 17], [9, 20], [12, 15], [1]]]
 h' := ![![[13, 22], [5, 12], [0, 7], [19, 13], [0, 1]], ![[0, 1], [0, 11], [22, 16], [4, 10], [13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [7, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [4, 10, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-132769, -7924, -57849, -152406, 117030]
  a := ![-45, -32, -57, -62, 159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12724, 147400, -57849, -152406, 117030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, -3, 2, 4]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![5, -1, -3, 2, 4]] 
 ![![23, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![5, -1, -3, 2, 4], ![-20, -2, -15, -30, 26], ![-44, 25, 88, 38, -132], ![140, -20, -28, 95, 27], ![28, -12, -40, -10, 59]]]
  hmulB := by decide  
  f := ![![![419, 105, -91, 30, -292]], ![![285, 71, -60, 20, -194]], ![![383, 102, -77, 28, -256]], ![![377, 95, -81, 27, -261]], ![![275, 73, -55, 20, -183]]]
  g := ![![![-1, -1, -3, 2, 4], ![25, -2, -15, -30, 26], ![-45, 25, 88, 38, -132], ![-64, -20, -28, 95, 27], ![15, -12, -40, -10, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![21, 20, 6, 4, 1]] ![![5039, -5807, -169, -1594, 2541]]
  ![![419, 105, -91, 30, -292]] where
 M := ![![![419, 105, -91, 30, -292]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![419, 105, -91, 30, -292]] ![![5, -1, -3, 2, 4]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB312I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB312I0 : PrimesBelowBoundCertificateInterval O 1 23 312 where
  m := 9
  g := ![5, 1, 5, 3, 5, 3, 1, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB312I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2, I11N3, I11N4]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0]
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
    · exact ![49, 7, 49]
    · exact ![11, 11, 11, 11, 11]
    · exact ![169, 169, 13]
    · exact ![1419857]
    · exact ![2476099]
    · exact ![529, 529, 23]
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
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
      exact NI11N3
      exact NI11N4
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I11N2, I11N3, I11N4, I13N0, I13N1, I13N2, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1, I11N2, I11N3, I11N4], [I13N0, I13N1, I13N2], [], [], [I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
