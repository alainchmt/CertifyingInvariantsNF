
import IdealArithmetic.Examples.NF3_3_670761_3.RI3_3_670761_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![40, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![40, 1, 0]] 
 ![![139, 0, 0], ![40, 1, 0], ![6, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![40, 1, 0], ![2, 41, 5], ![309, 54, 39]]]
  hmulB := by decide  
  f := ![![![-12163, -281303, -34310], ![-5421, 953818, 0]], ![![-3508, -80923, -9870], ![-1528, 274386, 0]], ![![-542, -12143, -1481], ![-175, 41172, 0]]]
  g := ![![![1, 0, 0], ![-40, 139, 0], ![-6, 0, 139]], ![![0, 1, 0], ![-12, 41, 5], ![-15, 54, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-38, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-38, 1, 0]] 
 ![![139, 0, 0], ![101, 1, 0], ![25, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-38, 1, 0], ![2, -37, 5], ![309, 54, -39]]]
  hmulB := by decide  
  f := ![![![8523, -175207, 23680], ![-3475, -658304, 0]], ![![6199, -127299, 17205], ![-2501, -478299, 0]], ![![1531, -31512, 4259], ![-632, -118400, 0]]]
  g := ![![![1, 0, 0], ![-101, 139, 0], ![-25, 0, 139]], ![![-1, 1, 0], ![26, -37, 5], ![-30, 54, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-2, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-2, 1, 0]] 
 ![![139, 0, 0], ![137, 1, 0], ![0, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-2, 1, 0], ![2, -1, 5], ![309, 54, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![28, 28, 0]]]
  g := ![![![1, 0, 0], ![-137, 139, 0], ![0, 0, 139]], ![![-1, 1, 0], ![1, -1, 5], ![-51, 54, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![40, 1, 0]] ![![139, 0, 0], ![-38, 1, 0]]
  ![![139, 0, 0], ![30, -55, 1]] where
 M := ![![![19321, 0, 0], ![-5282, 139, 0]], ![![5560, 139, 0], ![-1518, 3, 5]]]
 hmul := by decide  
 g := ![![![![109, 55, -1], ![139, 0, 0]], ![![-38, 1, 0], ![0, 0, 0]]], ![![![10, 56, -1], ![139, 0, 0]], ![![-12, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![30, -55, 1]] ![![139, 0, 0], ![-2, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-278, 139, 0]], ![![4170, -7645, 139], ![139, 139, -278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-2, 1, 0]]], ![![![30, -55, 1]], ![![1, 1, -2]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [112, 32, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 76, 106], [58, 72, 43], [0, 1]]
 g := ![![[32, 7, 82], [112, 4], [27, 4, 47], [13, 102], [17, 71, 53], [50, 1], []], ![[109, 7, 17, 87], [16, 123], [43, 66, 60, 90], [63, 143], [102, 17, 52, 56], [46, 118], [90, 61]], ![[108, 57, 11, 62], [66, 17], [145, 94, 84, 87], [23, 42], [52, 93, 97, 41], [42, 114], [4, 61]]]
 h' := ![![[141, 76, 106], [120, 141, 23], [105, 22, 147], [80, 137, 135], [33, 116, 129], [62, 76, 84], [0, 0, 1], [0, 1]], ![[58, 72, 43], [21, 7, 63], [144, 135, 102], [42, 100, 104], [63, 2, 128], [109, 2, 98], [116, 98, 72], [141, 76, 106]], ![[0, 1], [121, 1, 63], [19, 141, 49], [131, 61, 59], [144, 31, 41], [137, 71, 116], [85, 51, 76], [58, 72, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 7], []]
 b := ![[], [0, 114, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [112, 32, 99, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3461121, -918883, -264475]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23229, -6167, -1775]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![3, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![3, 1, 0]] 
 ![![151, 0, 0], ![3, 1, 0], ![149, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![3, 1, 0], ![2, 4, 5], ![309, 54, 2]]]
  hmulB := by decide  
  f := ![![![21398, 42819, 53530], ![755, -1616606, 0]], ![![421, 847, 1060], ![152, -32012, 0]], ![![21115, 42252, 52821], ![724, -1595194, 0]]]
  g := ![![![1, 0, 0], ![-3, 151, 0], ![-149, 0, 151]], ![![0, 1, 0], ![-5, 4, 5], ![-1, 54, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![28, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![28, 1, 0]] 
 ![![151, 0, 0], ![28, 1, 0], ![140, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![28, 1, 0], ![2, 29, 5], ![309, 54, 27]]]
  hmulB := by decide  
  f := ![![![-7437, -113521, -19575], ![-2114, 591165, 0]], ![![-1394, -21023, -3625], ![-301, 109475, 0]], ![![-6916, -105252, -18149], ![-1848, 548100, 0]]]
  g := ![![![1, 0, 0], ![-28, 151, 0], ![-140, 0, 151]], ![![0, 1, 0], ![-10, 29, 5], ![-33, 54, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-31, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-31, 1, 0]] 
 ![![151, 0, 0], ![120, 1, 0], ![56, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-31, 1, 0], ![2, -30, 5], ![309, 54, -32]]]
  hmulB := by decide  
  f := ![![![27192, -433385, 72240], ![-8305, -2181648, 0]], ![![21599, -344386, 57405], ![-6643, -1733631, 0]], ![![10098, -160726, 26791], ![-3014, -809088, 0]]]
  g := ![![![1, 0, 0], ![-120, 151, 0], ![-56, 0, 151]], ![![-1, 1, 0], ![22, -30, 5], ![-29, 54, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![3, 1, 0]] ![![151, 0, 0], ![28, 1, 0]]
  ![![151, 0, 0], ![-13, -54, 1]] where
 M := ![![![22801, 0, 0], ![4228, 151, 0]], ![![453, 151, 0], ![86, 32, 5]]]
 hmul := by decide  
 g := ![![![![151, 0, 0], ![0, 0, 0]], ![![28, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![1, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-13, -54, 1]] ![![151, 0, 0], ![-31, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-4681, 151, 0]], ![![-1963, -8154, 151], ![604, 1661, -302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-31, 1, 0]]], ![![![-13, -54, 1]], ![![4, 11, -2]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [36, 75, 151, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 85, 27], [90, 71, 130], [0, 1]]
 g := ![![[107, 40, 47], [151, 64], [35, 12, 101], [36, 39, 156], [99, 91, 108], [6, 1], []], ![[23, 55, 96, 39], [67, 64], [26, 56, 146, 147], [117, 151, 46, 147], [58, 124, 79, 126], [134, 17], [15, 101]], ![[12, 101, 6, 93], [122, 99], [109, 156, 73, 57], [94, 145, 24, 111], [50, 41, 54, 86], [119, 3], [69, 101]]]
 h' := ![![[73, 85, 27], [75, 68, 19], [153, 113, 8], [117, 146, 27], [47, 2, 129], [98, 142, 118], [0, 0, 1], [0, 1]], ![[90, 71, 130], [103, 77, 45], [85, 147, 8], [34, 75, 50], [22, 146, 107], [4, 127, 123], [79, 113, 71], [73, 85, 27]], ![[0, 1], [16, 12, 93], [144, 54, 141], [39, 93, 80], [136, 9, 78], [152, 45, 73], [121, 44, 85], [90, 71, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148, 32], []]
 b := ![[], [155, 99, 150], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [36, 75, 151, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19664250, 13531830, 7606807]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![125250, 86190, 48451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [79, 116, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 158, 55], [78, 4, 108], [0, 1]]
 g := ![![[12, 60, 150], [77, 156, 60], [125, 113], [98, 69], [84, 62], [138, 108, 1], []], ![[26, 35, 140, 90], [113, 101, 74, 144], [65, 115], [61, 104], [], [39, 108, 89, 65], [150, 91]], ![[121, 102, 49, 98], [5, 29, 71, 79], [119, 34], [49, 6], [61, 62], [6, 8, 140, 92], [97, 91]]]
 h' := ![![[30, 158, 55], [111, 74, 98], [38, 128, 95], [123, 1, 73], [82, 31, 118], [19, 73, 15], [0, 0, 1], [0, 1]], ![[78, 4, 108], [141, 129, 61], [145, 35, 85], [155, 59, 21], [35, 40, 58], [144, 59], [134, 50, 4], [30, 158, 55]], ![[0, 1], [123, 123, 4], [34, 0, 146], [12, 103, 69], [42, 92, 150], [121, 31, 148], [51, 113, 158], [78, 4, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 78], []]
 b := ![[], [109, 135, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [79, 116, 55, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81706261178, -23526685033, -7763762861]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-501265406, -144335491, -47630447]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [21, 148, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 25, 154], [131, 141, 13], [0, 1]]
 g := ![![[42, 67, 87], [50, 33, 133], [63, 57, 76], [5, 32], [153, 27], [61, 84, 1], []], ![[119, 123, 164, 126], [37, 125, 150, 19], [29, 42, 145, 116], [61, 133], [102, 28], [74, 142, 99, 63], [19, 2]], ![[45, 159, 166, 95], [166, 145, 51, 45], [135, 12, 54, 59], [35, 147], [25, 94], [40, 2, 102, 109], [160, 2]]]
 h' := ![![[120, 25, 154], [119, 92, 134], [13, 4, 48], [2, 28, 57], [146, 85, 52], [55, 63, 19], [0, 0, 1], [0, 1]], ![[131, 141, 13], [26, 18, 163], [32, 140, 36], [153, 163, 158], [91, 53, 48], [88, 60, 23], [140, 140, 141], [120, 25, 154]], ![[0, 1], [123, 57, 37], [162, 23, 83], [83, 143, 119], [145, 29, 67], [154, 44, 125], [107, 27, 25], [131, 141, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 8], []]
 b := ![[], [68, 149, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [21, 148, 83, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31651176, -12883716, -5555756]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-189528, -77148, -33268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![4, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![4, 1, 0]] 
 ![![173, 0, 0], ![4, 1, 0], ![31, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![4, 1, 0], ![2, 5, 5], ![309, 54, 3]]]
  hmulB := by decide  
  f := ![![![40005, 100091, 100100], ![1557, -3463460, 0]], ![![920, 2309, 2310], ![174, -79926, 0]], ![![7167, 17935, 17937], ![345, -620620, 0]]]
  g := ![![![1, 0, 0], ![-4, 173, 0], ![-31, 0, 173]], ![![0, 1, 0], ![-1, 5, 5], ![0, 54, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![59, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![59, 1, 0]] 
 ![![173, 0, 0], ![59, 1, 0], ![19, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![59, 1, 0], ![2, 60, 5], ![309, 54, 58]]]
  hmulB := by decide  
  f := ![![![-5098, -179505, -14960], ![-2595, 517616, 0]], ![![-1745, -61195, -5100], ![-864, 176460, 0]], ![![-594, -19715, -1643], ![-185, 56848, 0]]]
  g := ![![![1, 0, 0], ![-59, 173, 0], ![-19, 0, 173]], ![![0, 1, 0], ![-21, 60, 5], ![-23, 54, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-63, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-63, 1, 0]] 
 ![![173, 0, 0], ![110, 1, 0], ![15, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-63, 1, 0], ![2, -62, 5], ![309, 54, -64]]]
  hmulB := by decide  
  f := ![![![42832, -1606897, 129600], ![-24739, -4484160, 0]], ![![27228, -1021669, 82400], ![-15742, -2851040, 0]], ![![3756, -139327, 11237], ![-2029, -388800, 0]]]
  g := ![![![1, 0, 0], ![-110, 173, 0], ![-15, 0, 173]], ![![-1, 1, 0], ![39, -62, 5], ![-27, 54, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![4, 1, 0]] ![![173, 0, 0], ![59, 1, 0]]
  ![![173, 0, 0], ![13, 82, 1]] where
 M := ![![![29929, 0, 0], ![10207, 173, 0]], ![![692, 173, 0], ![238, 64, 5]]]
 hmul := by decide  
 g := ![![![![160, -82, -1], ![173, 0, 0]], ![![46, -81, -1], ![173, 0, 0]]], ![![![-9, -81, -1], ![173, 0, 0]], ![![1, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![13, 82, 1]] ![![173, 0, 0], ![-63, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-10899, 173, 0]], ![![2249, 14186, 173], ![-346, -5017, 346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-63, 1, 0]]], ![![![13, 82, 1]], ![![-2, -29, 2]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [24, 163, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 120, 19], [111, 58, 160], [0, 1]]
 g := ![![[5, 31, 65], [31, 129, 20], [123, 67], [29, 68], [84, 24, 15], [97, 170, 1], []], ![[11, 168, 138, 95], [130, 15, 28, 61], [175, 65], [169, 52], [14, 157, 41, 138], [138, 17, 51, 13], [58, 3]], ![[31, 71, 97, 163], [23, 120, 47, 18], [153, 39], [125, 139], [168, 46, 77, 50], [77, 49, 152, 91], [96, 3]]]
 h' := ![![[59, 120, 19], [151, 31, 85], [29, 16, 60], [81, 115, 109], [132, 53, 28], [178, 157, 33], [0, 0, 1], [0, 1]], ![[111, 58, 160], [8, 51, 149], [118, 4, 25], [77, 164, 94], [175, 72, 125], [155, 101, 64], [120, 159, 58], [59, 120, 19]], ![[0, 1], [133, 97, 124], [132, 159, 94], [90, 79, 155], [91, 54, 26], [11, 100, 82], [172, 20, 120], [111, 58, 160]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 92], []]
 b := ![[], [133, 83, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [24, 163, 9, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3789251, -1132175, -388430]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21169, -6325, -2170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![9, 1, 0]] 
 ![![181, 0, 0], ![9, 1, 0], ![91, 0, 1]] where
  M :=![![![9, 1, 0], ![2, 10, 5], ![309, 54, 8]]]
  hmulB := by decide  
  f := ![![![190, 8, -5]], ![![1, 0, 0]], ![![112, 5, -3]]]
  g := ![![![0, 1, 0], ![-3, 10, 5], ![-5, 54, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -2, 1]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-27, -2, 1]] 
 ![![181, 0, 0], ![63, 1, 0], ![99, 0, 1]] where
  M :=![![![-27, -2, 1], ![305, 25, -11], ![-720, -57, 29]]]
  hmulB := by decide  
  f := ![![![-98, -1, 3]], ![![-29, 0, 1]], ![![-57, 0, 2]]]
  g := ![![![0, -2, 1], ![-1, 25, -11], ![0, -57, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -1, 1]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-45, -1, 1]] 
 ![![181, 0, 0], ![109, 1, 0], ![64, 0, 1]] where
  M :=![![![-45, -1, 1], ![307, 8, -6], ![-411, -3, 10]]]
  hmulB := by decide  
  f := ![![![62, 7, -2]], ![![34, 4, -1]], ![![35, 4, -1]]]
  g := ![![![0, -1, 1], ![-1, 8, -6], ![-4, -3, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![9, 1, 0]] ![![-27, -2, 1]]
  ![![62, 7, -2]] where
 M := ![![![62, 7, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![62, 7, -2]] ![![-45, -1, 1]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)


lemma PB183I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 182 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 182 (by omega)

def PB183I3 : PrimesBelowBoundCertificateInterval O 137 182 183 where
  m := 9
  g := ![3, 1, 3, 1, 1, 1, 3, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB183I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![173, 173, 173]
    · exact ![5735339]
    · exact ![181, 181, 181]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
  β := ![I139N0, I139N1, I139N2, I151N0, I151N1, I151N2, I173N0, I173N1, I173N2, I181N0, I181N1, I181N2]
  Il := ![[I139N0, I139N1, I139N2], [], [I151N0, I151N1, I151N2], [], [], [], [I173N0, I173N1, I173N2], [], [I181N0, I181N1, I181N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
