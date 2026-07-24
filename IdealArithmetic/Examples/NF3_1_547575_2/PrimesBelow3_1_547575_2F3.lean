
import IdealArithmetic.Examples.NF3_1_547575_2.RI3_1_547575_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-993025019, 1546424924, -702244048]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-993025019, 1546424924, -702244048]] 
 ![![139, 0, 0], ![0, 139, 0], ![88, 57, 1]] where
  M :=![![![-993025019, 1546424924, -702244048], ![-16853857152, 29345405873, 3092849848], ![45541126752, -71830350460, 27798980949]]]
  hmulB := by decide  
  f := ![![![7467142930260413263, 53621576078807836, 182665443896369104]], ![![4383970653512858496, 31481306588087835, 107243152157615672]], ![![6518631925268232088, 46810315668930965, 159462435009883845]]]
  g := ![![![437442095, 299095940, -702244048], ![-2079313984, -1057172917, 3092849848], ![-17271720840, -11916347227, 27798980949]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [58, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 138], [0, 1]]
 g := ![![[11, 117], [99, 57], [116], [75, 89], [44], [52], [1]], ![[8, 22], [12, 82], [116], [5, 50], [44], [52], [1]]]
 h' := ![![[57, 138], [96, 16], [96, 14], [98, 33], [124, 111], [70, 105], [81, 57], [0, 1]], ![[0, 1], [35, 123], [60, 125], [33, 106], [57, 28], [78, 34], [133, 82], [57, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [2, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [58, 82, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![238, -544, -607]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![386, 245, -607]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1691162693, 3066451384, 900572974]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-1691162693, 3066451384, 900572974]] 
 ![![139, 0, 0], ![25, 1, 0], ![92, 0, 1]] where
  M :=![![![-1691162693, 3066451384, 900572974], ![21613751376, -35548203243, 6132902768], ![62787957528, -114917631056, -38614654627]]]
  hmulB := by decide  
  f := ![![![2077460248434191518369, 14918248358509473224, 50819999295775985594]], ![![382418605711895047579, 2746149169990089301, 9354938698643299182]], ![![1373198135431658526764, 9860939984412193968, 33591943974955156717]]]
  g := ![![![-1159749359, 3066451384, 900572974], ![2489868905, -35548203243, 6132902768], ![46678251508, -114917631056, -38614654627]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-993025019, 1546424924, -702244048]] ![![-1691162693, 3066451384, 900572974]]
  ![![139, 0, 0]] where
 M := ![![![-8989058765780681753, 22682531977083949860, 35706693579672963222]]]
 hmul := by decide  
 g := ![![![![-64669487523602027, 163183683288373740, 256882687623546498]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![43, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![43, 1, 0]] 
 ![![149, 0, 0], ![43, 1, 0], ![97, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![43, 1, 0], ![0, 44, 2], ![24, -41, 43]]]
  hmulB := by decide  
  f := ![![![1377, 32, 0], ![-4768, 0, 0]], ![![387, 9, 0], ![-1340, 0, 0]], ![![867, -2, -1], ![-3002, 75, 0]]]
  g := ![![![1, 0, 0], ![-43, 149, 0], ![-97, 0, 149]], ![![0, 1, 0], ![-14, 44, 2], ![-16, -41, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-22, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-22, 1, 0]] 
 ![![149, 0, 0], ![127, 1, 0], ![67, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-22, 1, 0], ![0, -21, 2], ![24, -41, -22]]]
  hmulB := by decide  
  f := ![![![1607, -73, 0], ![10877, 0, 0]], ![![1365, -62, 0], ![9239, 0, 0]], ![![761, -24, -1], ![5151, 75, 0]]]
  g := ![![![1, 0, 0], ![-127, 149, 0], ![-67, 0, 149]], ![![-1, 1, 0], ![17, -21, 2], ![45, -41, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![43, 1, 0]] ![![149, 0, 0], ![-22, 1, 0]]
  ![![149, 0, 0], ![-26, 11, 1]] where
 M := ![![![22201, 0, 0], ![-3278, 149, 0]], ![![6407, 149, 0], ![-946, 22, 2]]]
 hmul := by decide  
 g := ![![![![149, 0, 0], ![0, 0, 0]], ![![4, -10, -1], ![149, 0, 0]]], ![![![43, 1, 0], ![0, 0, 0]], ![![-6, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-26, 11, 1]] ![![149, 0, 0], ![-22, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-3278, 149, 0]], ![![-3874, 1639, 149], ![596, -298, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-22, 1, 0]]], ![![![-26, 11, 1]], ![![4, -2, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![43, 67, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![43, 67, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![43, 67, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![43, 67, 1], ![24, 69, 134], ![1596, -2735, 2]]]
  hmulB := by decide  
  f := ![![![-42, -67, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -67, 151]], ![![0, 0, 1], ![-38, -59, 134], ![10, -19, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [15, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 150], [0, 1]]
 g := ![![[122, 125], [120, 38], [114, 145], [64], [135, 49], [22], [1]], ![[137, 26], [40, 113], [71, 6], [64], [8, 102], [22], [1]]]
 h' := ![![[133, 150], [12, 124], [102, 75], [15, 121], [89, 8], [46, 144], [136, 133], [0, 1]], ![[0, 1], [45, 27], [111, 76], [102, 30], [96, 143], [21, 7], [7, 18], [133, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [72, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [15, 18, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2, -119, -590]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![168, 261, -590]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![17, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![17, 1, 0]] 
 ![![151, 0, 0], ![17, 1, 0], ![149, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![17, 1, 0], ![0, 18, 2], ![24, -41, 17]]]
  hmulB := by decide  
  f := ![![![1259, 74, 0], ![-11174, 0, 0]], ![![119, 7, 0], ![-1056, 0, 0]], ![![1243, 64, -1], ![-11032, 76, 0]]]
  g := ![![![1, 0, 0], ![-17, 151, 0], ![-149, 0, 151]], ![![0, 1, 0], ![-4, 18, 2], ![-12, -41, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![43, 67, 1]] ![![151, 0, 0], ![17, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![2567, 151, 0]], ![![6493, 10117, 151], ![755, 1208, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![17, 1, 0]]], ![![![43, 67, 1]], ![![5, 8, 1]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-16, -40, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-16, -40, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![141, 117, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-16, -40, 1], ![24, -97, -80], ![-972, 1652, -57]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-141, -117, 157]], ![![-1, -1, 1], ![72, 59, -80], ![45, 53, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [95, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 156], [0, 1]]
 g := ![![[11, 93], [4], [81, 109], [51, 12], [154, 76], [90], [1]], ![[9, 64], [4], [1, 48], [71, 145], [19, 81], [90], [1]]]
 h' := ![![[54, 156], [95, 67], [155, 155], [22, 100], [128, 13], [4, 95], [62, 54], [0, 1]], ![[0, 1], [102, 90], [47, 2], [84, 57], [45, 144], [110, 62], [152, 103], [54, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [120, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [95, 103, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2413, 12, -16]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 12, -16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-77, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-77, 1, 0]] 
 ![![157, 0, 0], ![80, 1, 0], ![57, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-77, 1, 0], ![0, -76, 2], ![24, -41, -77]]]
  hmulB := by decide  
  f := ![![![8779, -114, 0], ![17898, 0, 0]], ![![4544, -59, 0], ![9264, 0, 0]], ![![3253, -4, -1], ![6632, 79, 0]]]
  g := ![![![1, 0, 0], ![-80, 157, 0], ![-57, 0, 157]], ![![-1, 1, 0], ![38, -76, 2], ![49, -41, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-16, -40, 1]] ![![157, 0, 0], ![-77, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-12089, 157, 0]], ![![-2512, -6280, 157], ![1256, 2983, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-77, 1, 0]]], ![![![-16, -40, 1]], ![![8, 19, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-30, -33, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-30, -33, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![133, 130, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-30, -33, 1], ![24, -104, -66], ![-804, 1365, -71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-133, -130, 163]], ![![-1, -1, 1], ![54, 52, -66], ![53, 65, -71]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [48, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 162], [0, 1]]
 g := ![![[5, 119], [23, 96], [61], [126], [144], [87, 61], [1]], ![[133, 44], [129, 67], [61], [126], [144], [117, 102], [1]]]
 h' := ![![[86, 162], [37, 49], [87, 111], [9, 86], [29, 17], [62, 12], [115, 86], [0, 1]], ![[0, 1], [13, 114], [16, 52], [70, 77], [24, 146], [116, 151], [13, 77], [86, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [74, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [48, 77, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![306, -674, -1412]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1154, 1122, -1412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![66, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![66, 1, 0]] 
 ![![163, 0, 0], ![66, 1, 0], ![71, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![66, 1, 0], ![0, 67, 2], ![24, -41, 66]]]
  hmulB := by decide  
  f := ![![![1849, 28, 0], ![-4564, 0, 0]], ![![726, 11, 0], ![-1792, 0, 0]], ![![773, -22, -1], ![-1908, 82, 0]]]
  g := ![![![1, 0, 0], ![-66, 163, 0], ![-71, 0, 163]], ![![0, 1, 0], ![-28, 67, 2], ![-12, -41, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-30, -33, 1]] ![![163, 0, 0], ![66, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![10758, 163, 0]], ![![-4890, -5379, 163], ![-1956, -2282, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![66, 1, 0]]], ![![![-30, -33, 1]], ![![-12, -14, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [37, 24, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 113, 115], [101, 53, 52], [0, 1]]
 g := ![![[118, 154, 50], [112, 115, 44], [64, 85, 144], [51, 29], [1, 128], [60, 77, 1], []], ![[132, 104, 77, 28], [133, 49, 110, 6], [24, 143, 45, 107], [40, 1], [94, 44], [126, 23, 125, 57], [64, 32]], ![[64, 163, 137, 153], [92, 88, 57, 15], [138, 119, 6, 70], [88, 2], [151, 150], [66, 152, 19, 163], [127, 32]]]
 h' := ![![[143, 113, 115], [31, 136, 65], [137, 89, 82], [125, 133, 12], [26, 66, 153], [118, 53, 63], [0, 0, 1], [0, 1]], ![[101, 53, 52], [26, 34, 47], [21, 62, 52], [145, 133, 66], [150, 65, 1], [11, 96, 82], [45, 39, 53], [143, 113, 115]], ![[0, 1], [156, 164, 55], [38, 16, 33], [90, 68, 89], [138, 36, 13], [61, 18, 22], [158, 128, 113], [101, 53, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 146], []]
 b := ![[], [110, 85, 112], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [37, 24, 90, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47929, -97194, -75985]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![287, -582, -455]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![91, -55, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![91, -55, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![91, 118, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![91, -55, 1], ![24, -5, -110], ![-1332, 2267, 50]]]
  hmulB := by decide  
  f := ![![![-90, 55, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -118, 173]], ![![0, -1, 1], ![58, 75, -110], ![-34, -21, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [68, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 172], [0, 1]]
 g := ![![[3, 142], [37], [116, 90], [28, 24], [14], [29, 96], [1]], ![[99, 31], [37], [94, 83], [149, 149], [14], [167, 77], [1]]]
 h' := ![![[142, 172], [135, 90], [70, 146], [172, 104], [3, 71], [104, 138], [105, 142], [0, 1]], ![[0, 1], [113, 83], [42, 27], [62, 69], [51, 102], [151, 35], [28, 31], [142, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [68, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [68, 31, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14968, -28088, -16588]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8812, 11152, -16588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-63, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-63, 1, 0]] 
 ![![173, 0, 0], ![110, 1, 0], ![123, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-63, 1, 0], ![0, -62, 2], ![24, -41, -63]]]
  hmulB := by decide  
  f := ![![![5230, -83, 0], ![14359, 0, 0]], ![![3340, -53, 0], ![9170, 0, 0]], ![![3792, -29, -1], ![10411, 87, 0]]]
  g := ![![![1, 0, 0], ![-110, 173, 0], ![-123, 0, 173]], ![![-1, 1, 0], ![38, -62, 2], ![71, -41, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![91, -55, 1]] ![![173, 0, 0], ![-63, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-10899, 173, 0]], ![![15743, -9515, 173], ![-5709, 3460, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-63, 1, 0]]], ![![![91, -55, 1]], ![![-33, 20, -1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-39, 41, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-39, 41, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![140, 41, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-39, 41, 1], ![24, -39, 82], ![972, -1669, -80]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-140, -41, 179]], ![![-1, 0, 1], ![-64, -19, 82], ![68, 9, -80]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [163, 166, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 178], [0, 1]]
 g := ![![[12, 17], [60, 169], [144], [147], [136, 161], [107, 169], [1]], ![[54, 162], [109, 10], [144], [147], [81, 18], [156, 10], [1]]]
 h' := ![![[13, 178], [65, 165], [34, 166], [93, 12], [28, 46], [101, 55], [16, 13], [0, 1]], ![[0, 1], [62, 14], [44, 13], [70, 167], [89, 133], [100, 124], [6, 166], [13, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [103, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [163, 166, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![82, 180, 131]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, -29, 131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-82, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-82, 1, 0]] 
 ![![179, 0, 0], ![97, 1, 0], ![80, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-82, 1, 0], ![0, -81, 2], ![24, -41, -82]]]
  hmulB := by decide  
  f := ![![![13203, -161, 0], ![28819, 0, 0]], ![![7217, -88, 0], ![15753, 0, 0]], ![![5964, -32, -1], ![13018, 90, 0]]]
  g := ![![![1, 0, 0], ![-97, 179, 0], ![-80, 0, 179]], ![![-1, 1, 0], ![43, -81, 2], ![59, -41, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-39, 41, 1]] ![![179, 0, 0], ![-82, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-14678, 179, 0]], ![![-6981, 7339, 179], ![3222, -3401, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-82, 1, 0]]], ![![![-39, 41, 1]], ![![18, -19, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1222855909, -8781332, -29914188]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-1222855909, -8781332, -29914188]] 
 ![![181, 0, 0], ![0, 181, 0], ![144, 166, 1]] where
  M :=![![![-1222855909, -8781332, -29914188], ![-717940512, -5155533, -17562664], ![148218288, 1064356, 3625799]]]
  hmulB := by decide  
  f := ![![![-2257, 3860, 76]], ![![1824, -1513, 7720]], ![![384, 814, 7111]]]
  g := ![![![17043023, 27386596, -29914188], ![10005984, 16078711, -17562664], ![-2065728, -3319438, 3625799]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [26, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 180], [0, 1]]
 g := ![![[32, 37], [122], [145, 119], [11], [147, 55], [53, 80], [1]], ![[18, 144], [122], [144, 62], [11], [180, 126], [101, 101], [1]]]
 h' := ![![[73, 180], [142, 134], [31, 22], [155, 32], [160, 83], [70, 112], [155, 73], [0, 1]], ![[0, 1], [150, 47], [8, 159], [138, 149], [65, 98], [101, 69], [54, 108], [73, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [95, 166]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [26, 108, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![446, -597, -467]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![374, 425, -467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2257, -3860, -76]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![2257, -3860, -76]] 
 ![![181, 0, 0], ![30, 1, 0], ![78, 0, 1]] where
  M :=![![![2257, -3860, -76], ![-1824, 1513, -7720], ![-91728, 157348, 5373]]]
  hmulB := by decide  
  f := ![![![1222855909, 8781332, 29914188]], ![![206649822, 1483953, 5055184]], ![![526157694, 3778340, 12871165]]]
  g := ![![![685, -3860, -76], ![3066, 1513, -7720], ![-28902, 157348, 5373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-1222855909, -8781332, -29914188]] ![![2257, -3860, -76]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-67, -80, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-67, -80, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![124, 111, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-67, -80, 1], ![24, -188, -160], ![-1932, 3292, -108]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-124, -111, 191]], ![![-1, -1, 1], ![104, 92, -160], ![60, 80, -108]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [31, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 190], [0, 1]]
 g := ![![[182, 75], [34, 130], [41, 162], [18, 163], [72, 16], [67, 104], [1]], ![[97, 116], [14, 61], [163, 29], [37, 28], [143, 175], [51, 87], [1]]]
 h' := ![![[88, 190], [92, 71], [66, 148], [15, 131], [60, 113], [24, 4], [160, 88], [0, 1]], ![[0, 1], [37, 120], [102, 43], [83, 60], [72, 78], [185, 187], [73, 103], [88, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153]]
 b := ![[], [72, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [31, 103, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2113, -4296, -1990]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1303, 1134, -1990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-31, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-31, 1, 0]] 
 ![![191, 0, 0], ![160, 1, 0], ![108, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-31, 1, 0], ![0, -30, 2], ![24, -41, -31]]]
  hmulB := by decide  
  f := ![![![2078, -67, 0], ![12797, 0, 0]], ![![1768, -57, 0], ![10888, 0, 0]], ![![1212, -24, -1], ![7464, 96, 0]]]
  g := ![![![1, 0, 0], ![-160, 191, 0], ![-108, 0, 191]], ![![-1, 1, 0], ![24, -30, 2], ![52, -41, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-67, -80, 1]] ![![191, 0, 0], ![-31, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-5921, 191, 0]], ![![-12797, -15280, 191], ![2101, 2292, -191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-31, 1, 0]]], ![![![-67, -80, 1]], ![![11, 12, -1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-65, -18, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-65, -18, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![128, 175, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-65, -18, 1], ![24, -124, -36], ![-444, 750, -106]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-128, -175, 193]], ![![-1, -1, 1], ![24, 32, -36], ![68, 100, -106]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [86, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 192], [0, 1]]
 g := ![![[161, 101], [186], [43], [92], [86], [147], [50, 1]], ![[0, 92], [186], [43], [92], [86], [147], [100, 192]]]
 h' := ![![[50, 192], [153, 78], [138, 147], [180, 129], [117, 51], [117, 47], [139, 98], [0, 1]], ![[0, 1], [0, 115], [154, 46], [68, 64], [158, 142], [151, 146], [21, 95], [50, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [60, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [86, 143, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2102, 12, 128]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74, -116, 128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![36, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![36, 1, 0]] 
 ![![193, 0, 0], ![36, 1, 0], ![106, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![36, 1, 0], ![0, 37, 2], ![24, -41, 36]]]
  hmulB := by decide  
  f := ![![![1621, 45, 0], ![-8685, 0, 0]], ![![252, 7, 0], ![-1350, 0, 0]], ![![850, 5, -1], ![-4554, 97, 0]]]
  g := ![![![1, 0, 0], ![-36, 193, 0], ![-106, 0, 193]], ![![0, 1, 0], ![-8, 37, 2], ![-12, -41, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-65, -18, 1]] ![![193, 0, 0], ![36, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![6948, 193, 0]], ![![-12545, -3474, 193], ![-2316, -772, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![36, 1, 0]]], ![![![-65, -18, 1]], ![![-12, -4, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB210I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB210I3 : PrimesBelowBoundCertificateInterval O 137 193 210 where
  m := 11
  g := ![2, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB210I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
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
      exact NI179N1
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
      exact NI193N1
  β := ![I139N1, I149N0, I149N1, I151N1, I157N1, I163N1, I173N1, I179N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N1], [I151N1], [I157N1], [I163N1], [], [I173N1], [I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
