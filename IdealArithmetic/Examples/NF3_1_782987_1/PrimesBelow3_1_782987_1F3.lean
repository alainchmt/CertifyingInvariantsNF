
import IdealArithmetic.Examples.NF3_1_782987_1.RI3_1_782987_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![305, -20, 6]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![305, -20, 6]] 
 ![![139, 0, 0], ![11, 1, 0], ![18, 0, 1]] where
  M :=![![![305, -20, 6], ![-708, 47, -14], ![1652, -106, 33]]]
  hmulB := by decide  
  f := ![![![67, 24, -2]], ![![7, 3, 0]], ![![-10, -2, 1]]]
  g := ![![![3, -20, 6], ![-7, 47, -14], ![16, -106, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6052800467454089, -2658058452836854, -23906733959488]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-6052800467454089, -2658058452836854, -23906733959488]] 
 ![![139, 0, 0], ![133, 1, 0], ![103, 0, 1]] where
  M :=![![![-6052800467454089, -2658058452836854, -23906733959488], ![2820994607219584, -5024810907196105, -2681965186796342], ![316471892041968356, 118145497639462290, -7706776093992447]]]
  hmulB := by decide  
  f := ![![![-355587204222178705608172436762115, 23309534321335559043564962949258, -7008693417423118121615108593828]], ![![-334288290203552805090189577520069, 21913343003342767815938253992977, -6588887651894692584552946680746]], ![![-277330800442777515873610387053515, 18179652514282414102114606191092, -5466244376716930589806684158535]]]
  g := ![![![2517491851494063, -2658058452836854, -23906733959488], ![6815563018016725, -5024810907196105, -2681965186796342], ![-105058139254138807, 118145497639462290, -7706776093992447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![305, -20, 6]] ![![-6052800467454089, -2658058452836854, -23906733959488]]
  ![![-3692682466078689, -1338624134544630, 107093314328318]] where
 M := ![![![-3692682466078689, -1338624134544630, 107093314328318]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-3692682466078689, -1338624134544630, 107093314328318]] ![![-6052800467454089, -2658058452836854, -23906733959488]]
  ![![139, 0, 0]] where
 M := ![![![52466842502724259832123461480609, 29194291909677189182303567998776, 2853079109675589578901895680546]]]
 hmul := by decide  
 g := ![![![![377459298580750070734701161731, 210030877048037332246788258984, 20525748990471867474114357414]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-535110561391, 35077690784, -10547133937]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-535110561391, 35077690784, -10547133937]] 
 ![![149, 0, 0], ![0, 149, 0], ![38, 90, 1]] where
  M :=![![![-535110561391, 35077690784, -10547133937], ![1244561804566, -81583802100, 24530556847], ![-2894605707946, 189747860145, -57053245253]]]
  hmulB := by decide  
  f := ![![![78735, 63037, 12548]], ![![-1480664, -460829, 75585]], ![![-934140, -294027, 46270]]]
  g := ![![![-901472965, 6606172786, -10547133937], ![2096648620, -15364657170, 24530556847], ![-4876391868, 35735167335, -57053245253]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [148, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 148], [0, 1]]
 g := ![![[112, 148], [33], [53, 96], [69], [30, 19], [28], [1]], ![[0, 1], [33], [77, 53], [69], [72, 130], [28], [1]]]
 h' := ![![[112, 148], [11, 105], [53, 35], [75, 29], [30, 48], [29, 82], [1, 112], [0, 1]], ![[0, 1], [0, 44], [99, 114], [45, 120], [42, 101], [124, 67], [29, 37], [112, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [78, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [148, 37, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-206, -284, -76]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 44, -76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78735, 63037, 12548]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![78735, 63037, 12548]] 
 ![![149, 0, 0], ![58, 1, 0], ![63, 0, 1]] where
  M :=![![![78735, 63037, 12548], ![-1480664, -460829, 75585], ![-8919030, -4730819, -385244]]]
  hmulB := by decide  
  f := ![![![-535110561391, 35077690784, -10547133937]], ![![-199945307088, 13106860828, -3940961151]], ![![-245681685071, 16104982413, -4842434116]]]
  g := ![![![-29315, 63037, 12548], ![137487, -460829, 75585], ![1944556, -4730819, -385244]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-535110561391, 35077690784, -10547133937]] ![![78735, 63037, 12548]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [136, 9, 109, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 148, 83], [123, 2, 68], [0, 1]]
 g := ![![[55, 9, 22], [143, 31, 74], [142, 116, 68], [67, 42], [120, 113, 78], [42, 1], []], ![[8, 41, 117, 3], [113, 2, 29, 6], [87, 73, 108, 120], [11, 8], [130, 120, 78, 51], [124, 4], [128, 94]], ![[22, 61, 36, 18], [12, 35, 51, 10], [19, 109, 114, 2], [91, 99], [45, 1, 139, 47], [10, 9], [143, 94]]]
 h' := ![![[70, 148, 83], [31, 38, 133], [16, 17, 136], [92, 149, 81], [139, 83, 58], [26, 90, 94], [0, 0, 1], [0, 1]], ![[123, 2, 68], [127, 84, 98], [76, 114, 22], [14, 21, 147], [0, 19, 59], [69, 55, 108], [25, 140, 2], [70, 148, 83]], ![[0, 1], [1, 29, 71], [150, 20, 144], [25, 132, 74], [87, 49, 34], [126, 6, 100], [60, 11, 148], [123, 2, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 25], []]
 b := ![[], [88, 62, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [136, 9, 109, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![413589, 174405, 8003]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2739, 1155, 53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, -14, -38]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![173, -14, -38]] 
 ![![157, 0, 0], ![0, 157, 0], ![107, 83, 1]] where
  M :=![![![173, -14, -38], ![4484, 1807, -52], ![6136, 6720, 1755]]]
  hmulB := by decide  
  f := ![![![22425, -1470, 442]], ![![-52156, 3419, -1028]], ![![-11517, 755, -227]]]
  g := ![![![27, 20, -38], ![64, 39, -52], ![-1157, -885, 1755]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [18, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 156], [0, 1]]
 g := ![![[86, 64], [109], [81, 11], [121, 126], [83, 126], [13], [1]], ![[81, 93], [109], [9, 146], [67, 31], [29, 31], [13], [1]]]
 h' := ![![[22, 156], [63, 149], [112, 100], [20, 47], [76, 122], [90, 122], [139, 22], [0, 1]], ![[0, 1], [44, 8], [114, 57], [112, 110], [91, 35], [105, 35], [152, 135], [22, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [138, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [18, 135, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4408, -68, -50]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 26, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22425, -1470, 442]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![22425, -1470, 442]] 
 ![![157, 0, 0], ![73, 1, 0], ![9, 0, 1]] where
  M :=![![![22425, -1470, 442], ![-52156, 3419, -1028], ![121304, -7952, 2391]]]
  hmulB := by decide  
  f := ![![![173, -14, -38]], ![![109, 5, -18]], ![![49, 42, 9]]]
  g := ![![![801, -1470, 442], ![-1863, 3419, -1028], ![4333, -7952, 2391]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![173, -14, -38]] ![![22425, -1470, 442]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [79, 39, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 61, 96], [54, 101, 67], [0, 1]]
 g := ![![[82, 39, 135], [118, 128, 93], [154, 121], [72, 113], [48, 118], [49, 96, 1], []], ![[51, 56, 144, 21], [146, 99, 159, 113], [83, 25], [123, 62], [117, 51], [12, 49, 115, 155], [111, 88]], ![[149, 71, 25, 42], [36, 111, 161, 50], [17, 36], [97, 83], [69, 136], [109, 129, 52, 80], [140, 88]]]
 h' := ![![[42, 61, 96], [132, 13, 61], [100, 51, 16], [81, 32, 152], [8, 114, 90], [41, 122, 66], [0, 0, 1], [0, 1]], ![[54, 101, 67], [107, 116, 74], [24, 117, 155], [77, 78, 5], [103, 15, 148], [50, 104, 122], [4, 37, 101], [42, 61, 96]], ![[0, 1], [59, 34, 28], [16, 158, 155], [113, 53, 6], [21, 34, 88], [16, 100, 138], [6, 126, 61], [54, 101, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 46], []]
 b := ![[], [142, 110, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [79, 39, 67, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-536596, -405707, -72535]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3292, -2489, -445]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [97, 20, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 116, 149], [119, 50, 18], [0, 1]]
 g := ![![[83, 55, 84], [96, 125, 9], [43, 137, 42], [137, 98], [37, 31], [22, 84, 1], []], ![[29, 92, 155, 71], [163, 43, 23, 10], [99, 52, 96, 134], [25, 85], [128, 58], [155, 130, 42, 90], [161, 157]], ![[69, 17, 129, 133], [40, 155, 1, 22], [165, 152, 35, 61], [161, 49], [60, 130], [123, 105, 2, 58], [125, 157]]]
 h' := ![![[132, 116, 149], [40, 166, 77], [4, 133, 164], [134, 116, 84], [118, 17, 91], [37, 96, 71], [0, 0, 1], [0, 1]], ![[119, 50, 18], [103, 155, 27], [115, 112, 128], [67, 88, 108], [133, 15, 69], [58, 147, 152], [137, 151, 50], [132, 116, 149]], ![[0, 1], [47, 13, 63], [37, 89, 42], [93, 130, 142], [43, 135, 7], [39, 91, 111], [32, 16, 116], [119, 50, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113, 72], []]
 b := ![[], [3, 2, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [97, 20, 83, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67635, -38744, -4008]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-405, -232, -24]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15919886733, -5123985976, 739921948]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-15919886733, -5123985976, 739921948]] 
 ![![173, 0, 0], ![0, 173, 0], ![107, 27, 1]] where
  M :=![![![-15919886733, -5123985976, 739921948], ![-87310789864, -47736530497, -4384064028], ![517319555304, 101203963340, -52120594525]]]
  hmulB := by decide  
  f := ![![![-16946479799042534465, 1110879547439473960, -334018434875489708]], ![![39414175315307785544, -2583687099396477021, 776861112563984252]], ![![-4859885643160642311, 318576343164019057, -95789297568105877]]]
  g := ![![![-549662053, -145097564, 739921948], ![2206844284, 408284383, -4384064028], ![35226723523, 8719422055, -52120594525]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [32, 169, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 172], [0, 1]]
 g := ![![[108, 78], [51], [132, 24], [76, 54], [142], [154, 16], [1]], ![[74, 95], [51], [55, 149], [119, 119], [142], [45, 157], [1]]]
 h' := ![![[4, 172], [92, 123], [101, 33], [163, 102], [90, 153], [89, 90], [141, 4], [0, 1]], ![[0, 1], [65, 50], [60, 140], [52, 71], [10, 20], [103, 83], [157, 169], [4, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [105, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [32, 169, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4400, 1454, 528]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-352, -74, 528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16946479799042534465, 1110879547439473960, -334018434875489708]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-16946479799042534465, 1110879547439473960, -334018434875489708]] 
 ![![173, 0, 0], ![145, 1, 0], ![81, 0, 1]] where
  M :=![![![-16946479799042534465, 1110879547439473960, -334018434875489708], ![39414175315307785544, -2583687099396477021, 776861112563984252], ![-91669611282550141736, 6009147475056462708, -1806825986832492769]]]
  hmulB := by decide  
  f := ![![![-15919886733, -5123985976, 739921948]], ![![-13847944313, -4570604029, 594824384]], ![![-4463533353, -1814097692, 45162331]]]
  g := ![![![-872650410132090129, 1110879547439473960, -334018434875489708], ![2029613032428405949, -2583687099396477021, 776861112563984252], ![-4720480290360146359, 6009147475056462708, -1806825986832492769]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-15919886733, -5123985976, 739921948]] ![![-16946479799042534465, 1110879547439473960, -334018434875489708]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [65, 34, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 116, 110], [71, 62, 69], [0, 1]]
 g := ![![[154, 46, 101], [178, 58, 172], [7, 172], [53, 173], [53, 68, 12], [31, 85, 1], []], ![[172, 9, 19, 138], [169, 95, 1, 59], [24, 60], [124, 17], [83, 48, 72, 76], [33, 80, 90, 42], [68, 107]], ![[98, 40, 96, 30], [91, 121, 172, 7], [8, 70], [156, 158], [174, 160, 124, 154], [74, 142, 115, 170], [109, 107]]]
 h' := ![![[14, 116, 110], [65, 99, 97], [104, 145, 72], [102, 126, 72], [135, 11, 50], [133, 44, 38], [0, 0, 1], [0, 1]], ![[71, 62, 69], [22, 83, 78], [158, 164, 8], [69, 108, 66], [130, 151, 14], [84, 132, 36], [72, 67, 62], [14, 116, 110]], ![[0, 1], [177, 176, 4], [166, 49, 99], [68, 124, 41], [30, 17, 115], [49, 3, 105], [104, 112, 116], [71, 62, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 144], []]
 b := ![[], [16, 147, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [65, 34, 94, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74464, 13067, -5549]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![416, 73, -31]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4200651, 11687045, 4248398]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![4200651, 11687045, 4248398]] 
 ![![181, 0, 0], ![0, 181, 0], ![133, 9, 1]] where
  M :=![![![4200651, 11687045, 4248398], ![-501310964, -178480463, 15935443], ![-1880382274, -1186535013, -162545020]]]
  hmulB := by decide  
  f := ![![![-264746251354199, 17354707253554, -5218200450189]], ![![615747653122302, -40363631996072, 12136506803365]], ![![-171832211904999, 11263984736661, -3386846540539]]]
  g := ![![![-3098543, -146677, 4248398], ![-14479143, -1778450, 15935443], ![109050306, 1526907, -162545020]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [77, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [164, 180], [0, 1]]
 g := ![![[106, 29], [64], [89, 42], [3], [163, 12], [58, 108], [1]], ![[156, 152], [64], [99, 139], [3], [140, 169], [32, 73], [1]]]
 h' := ![![[164, 180], [41, 36], [25, 8], [174, 59], [119, 148], [59, 66], [104, 164], [0, 1]], ![[0, 1], [153, 145], [70, 173], [76, 122], [137, 33], [23, 115], [31, 17], [164, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [39, 143]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [77, 17, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-867, -799, -129]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![90, 2, -129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-264746251354199, 17354707253554, -5218200450189]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-264746251354199, 17354707253554, -5218200450189]] 
 ![![181, 0, 0], ![171, 1, 0], ![81, 0, 1]] where
  M :=![![![-264746251354199, 17354707253554, -5218200450189], ![615747653122302, -40363631996072, 12136506803365], ![-1432107802797070, 93877860577607, -28227125192707]]]
  hmulB := by decide  
  f := ![![![4200651, 11687045, 4248398]], ![![1198897, 10055272, 4101721]], ![![-8509003, -1325328, 1003178]]]
  g := ![![![-15523353343904, 17354707253554, -5218200450189], ![36104263388829, -40363631996072, 12136506803365], ![-83971407850600, 93877860577607, -28227125192707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![4200651, 11687045, 4248398]] ![![-264746251354199, 17354707253554, -5218200450189]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19331150713, -7285496774, 441183369]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-19331150713, -7285496774, 441183369]] 
 ![![191, 0, 0], ![0, 191, 0], ![19, 33, 1]] where
  M :=![![![-19331150713, -7285496774, 441183369], ![-52059637542, -38302035580, -6844313405], ![807628981790, 242245838873, -45146348985]]]
  hmulB := by decide  
  f := ![![![17734049777144036015, -1162506516062169483, 349541593346150390]], ![![-41245908014845746020, 2703761263259569245, -812964922716019093]], ![![-4859885643160642311, 318576343164019057, -95789297568105877]]]
  g := ![![![-145097564, -114369361, 441183369], ![408284383, 981991135, -6844313405], ![8719422055, 9068457358, -45146348985]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [124, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 190], [0, 1]]
 g := ![![[5, 120], [97, 18], [189, 180], [84, 135], [80, 130], [86, 108], [1]], ![[95, 71], [15, 173], [133, 11], [42, 56], [82, 61], [167, 83], [1]]]
 h' := ![![[144, 190], [5, 87], [57, 20], [89, 84], [12, 53], [32, 43], [67, 144], [0, 1]], ![[0, 1], [118, 104], [72, 171], [152, 107], [4, 138], [112, 148], [175, 47], [144, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [167, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [124, 47, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4470, 566, -6]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24, 4, -6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17734049777144036015, -1162506516062169483, 349541593346150390]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![17734049777144036015, -1162506516062169483, 349541593346150390]] 
 ![![191, 0, 0], ![157, 1, 0], ![181, 0, 1]] where
  M :=![![![17734049777144036015, -1162506516062169483, 349541593346150390], ![-41245908014845746020, 2703761263259569245, -812964922716019093], ![95929860880490252974, -6288416338056925021, 1890796340543550152]]]
  hmulB := by decide  
  f := ![![![-19331150713, -7285496774, 441183369]], ![![-16162567013, -6189136278, 326814008]], ![![-14090624593, -5635754331, 181716444]]]
  g := ![![![717175625147913216, -1162506516062169483, 349541593346150390], ![-1668009294947636972, 2703761263259569245, -812964922716019093], ![3879461195377198449, -6288416338056925021, 1890796340543550152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-19331150713, -7285496774, 441183369]] ![![17734049777144036015, -1162506516062169483, 349541593346150390]]
  ![![191, 0, 0]] where
 M := ![![![191, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [172, 2, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 130, 121], [17, 62, 72], [0, 1]]
 g := ![![[144, 112, 72], [6, 81], [94, 4], [128, 8], [147, 84], [6, 86], [1]], ![[107, 6, 62, 168], [188, 97], [12, 110], [131, 107], [135, 118], [172, 185], [90, 51, 6, 14]], ![[152, 90, 140, 139], [72, 96], [173, 185], [81, 138], [20, 67], [0, 101], [62, 162, 75, 179]]]
 h' := ![![[129, 130, 121], [162, 112, 119], [187, 51, 9], [170, 26, 191], [143, 188, 104], [181, 166, 85], [21, 191, 146], [0, 1]], ![[17, 62, 72], [79, 160, 86], [143, 98, 167], [85, 28, 127], [187, 147, 53], [132, 183, 73], [103, 98, 125], [129, 130, 121]], ![[0, 1], [107, 114, 181], [116, 44, 17], [27, 139, 68], [177, 51, 36], [170, 37, 35], [39, 97, 115], [17, 62, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 98], []]
 b := ![[], [155, 141, 189], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [172, 2, 47, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29336, 0, 0]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![152, 0, 0]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB251I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB251I3 : PrimesBelowBoundCertificateInterval O 137 193 251 where
  m := 11
  g := ![3, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB251I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
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
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![7189057]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I149N1, I157N1, I173N1, I181N1, I191N1]
  Il := ![[I139N0, I139N1, I139N1], [I149N1], [], [I157N1], [], [], [I173N1], [], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
