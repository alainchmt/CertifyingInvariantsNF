
import IdealArithmetic.Examples.NF3_1_342171_1.RI3_1_342171_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [5, 123, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 71, 43], [95, 67, 96], [0, 1]]
 g := ![![[6, 125, 11], [21, 26, 55], [1, 1], [104, 14, 41], [89, 37], [65, 1], []], ![[53, 25, 115, 27], [58, 85, 60, 33], [92, 28], [11, 84, 107, 76], [74, 78], [69, 41], [79, 42]], ![[87, 66, 81, 96], [92, 96, 133, 25], [43, 52], [135, 10, 120, 29], [126, 5], [69, 37], [26, 42]]]
 h' := ![![[109, 71, 43], [34, 138, 17], [40, 70, 65], [36, 107, 1], [96, 137, 72], [92, 62, 71], [0, 0, 1], [0, 1]], ![[95, 67, 96], [31, 54, 123], [46, 76, 137], [111, 82, 81], [98, 44, 12], [32, 10, 56], [88, 130, 67], [109, 71, 43]], ![[0, 1], [61, 86, 138], [92, 132, 76], [53, 89, 57], [112, 97, 55], [73, 67, 12], [138, 9, 71], [95, 67, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 64], []]
 b := ![[], [41, 127, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [5, 123, 74, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-194739, 121208, -138166]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1401, 872, -994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [73, 134, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 36, 148], [103, 112, 1], [0, 1]]
 g := ![![[78, 105, 118], [81, 80], [109, 83, 120], [137, 116], [73, 74, 100], [71, 1], []], ![[62, 147, 94, 30], [41, 85], [79, 95, 32, 144], [140, 120], [50, 120, 56, 69], [47, 28], [148, 1]], ![[104, 30, 15, 76], [9, 142], [112, 135, 1, 129], [47, 49], [147, 114, 136, 104], [63, 104], [146, 1]]]
 h' := ![![[117, 36, 148], [71, 105, 72], [89, 122, 123], [15, 91, 92], [35, 144, 50], [32, 98, 139], [0, 0, 1], [0, 1]], ![[103, 112, 1], [3, 75, 62], [145, 130, 95], [134, 7, 81], [64, 16, 92], [81, 32, 123], [54, 141, 112], [117, 36, 148]], ![[0, 1], [57, 118, 15], [72, 46, 80], [112, 51, 125], [50, 138, 7], [37, 19, 36], [100, 8, 36], [103, 112, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 43], []]
 b := ![[], [95, 100, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [73, 134, 78, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10889218, -2317248, 598086]
  a := ![5, 0, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73082, -15552, 4014]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85206893751768, 4049232403661, 4532012743639]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![85206893751768, 4049232403661, 4532012743639]] 
 ![![151, 0, 0], ![0, 151, 0], ![72, 62, 1]] where
  M :=![![![85206893751768, 4049232403661, 4532012743639], ![447703700940305, 21275935000844, 23812614081988], ![247751135358669, 11773717843309, 13177470193522]]]
  hmulB := by decide  
  f := ![![![-2317124, 643559, -366048]], ![![-34219538, 3817155, 4870961]], ![![-14664275, 1771455, 1842213]]]
  g := ![![![-1596675654240, -1834010315907, 4532012743639], ![-8389433860681, -9636464490612, 23812614081988], ![-4642561050165, -5332645259305, 13177470193522]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [138, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 150], [0, 1]]
 g := ![![[65, 58], [66, 110], [24, 40], [58], [124, 95], [97], [1]], ![[0, 93], [0, 41], [0, 111], [58], [67, 56], [97], [1]]]
 h' := ![![[90, 150], [103, 71], [10, 67], [135, 74], [102, 71], [71, 47], [13, 90], [0, 1]], ![[0, 1], [0, 80], [0, 84], [0, 77], [150, 80], [73, 104], [110, 61], [90, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [106, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [138, 61, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1212212, 260176, -576686]
  a := ![-66, -64, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![283004, 238508, -576686]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2317124, -643559, 366048]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![2317124, -643559, 366048]] 
 ![![151, 0, 0], ![20, 1, 0], ![5, 0, 1]] where
  M :=![![![2317124, -643559, 366048], ![34219538, -3817155, -4870961], ![-74138759, 15510153, -2530037]]]
  hmulB := by decide  
  f := ![![![-85206893751768, -4049232403661, -4532012743639]], ![![-14250606463415, -677222404464, -757966019568]], ![![-4462156318659, -212052184514, -237334661667]]]
  g := ![![![88464, -643559, 366048], ![893493, -3817155, -4870961], ![-2461534, 15510153, -2530037]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![85206893751768, 4049232403661, 4532012743639]] ![![2317124, -643559, 366048]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![410881304110671116766, 19526047921784463289, 21854092132233548320]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![410881304110671116766, 19526047921784463289, 21854092132233548320]] 
 ![![157, 0, 0], ![50, 1, 0], ![107, 0, 1]] where
  M :=![![![410881304110671116766, 19526047921784463289, 21854092132233548320], ![2158899032670223113618, 102595970048952355255, 114828243320257694703], ![1194695700181619392793, 56774755288969823785, 63543874205383428677]]]
  hmulB := by decide  
  f := ![![![-29779263220, 12626452547, -12575163433]], ![![-17092363751, 5113358396, -3361769684]], ![![-9931274125, 6117395028, -7638985679]]]
  g := ![![![-18495598408455679732, 19526047921784463289, 21854092132233548320], ![-97181665637229095429, 102595970048952355255, 114828243320257694703], ![-53778577097088526528, 56774755288969823785, 63543874205383428677]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1160882536160, -55167874045, -61745408336]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-1160882536160, -55167874045, -61745408336]] 
 ![![157, 0, 0], ![124, 1, 0], ![141, 0, 1]] where
  M :=![![![-1160882536160, -55167874045, -61745408336], ![-6099640356682, -289869285165, -324429709979], ![-3375430715613, -160408422701, -179533537075]]]
  hmulB := by decide  
  f := ![![![-5159096, 682839, 540385]], ![![-3732133, 459172, 453804]], ![![-4321589, 603082, 396475]]]
  g := ![![![91630805228, -55167874045, -61745408336], ![481456943381, -289869285165, -324429709979], ![266429569598, -160408422701, -179533537075]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32020739400773701356, 1521701001664633693, 1703129789566336792]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![32020739400773701356, 1521701001664633693, 1703129789566336792]] 
 ![![157, 0, 0], ![140, 1, 0], ![96, 0, 1]] where
  M :=![![![32020739400773701356, 1521701001664633693, 1703129789566336792], ![168246991591263936210, 7995493558943283169, 8948777222086099059], ![93104843895346690877, 4424561608091883277, 4952091555614015783]]]
  hmulB := by decide  
  f := ![![![32916719984, -6080949235, -332058961]], ![![29069867389, -5219848648, -565113632]], ![![16438082353, -3171145423, 77075754]]]
  g := ![![![-2194381277902186928, 1521701001664633693, 1703129789566336792], ![-11529966369306122402, 7995493558943283169, 8948777222086099059], ![-6380474971824601803, 4424561608091883277, 4952091555614015783]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![410881304110671116766, 19526047921784463289, 21854092132233548320]] ![![-1160882536160, -55167874045, -61745408336]]
  ![![-669853774131924846874839286025818, -31833030034301958521119458958475, -35628406424304990090583772186307]] where
 M := ![![![-669853774131924846874839286025818, -31833030034301958521119458958475, -35628406424304990090583772186307]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-669853774131924846874839286025818, -31833030034301958521119458958475, -35628406424304990090583772186307]] ![![32020739400773701356, 1521701001664633693, 1703129789566336792]]
  ![![157, 0, 0]] where
 M := ![![![-30122201892983630741412086157808926674814926657710197, -1431478024888768795023696510284464413907761789781188, -1602149742052250591227224443786471923698651927354262]]]
 hmul := by decide  
 g := ![![![![-191861158554035864594981440495598259075254309921721, -9117694426043113344099977772512512190495298024084, -10204775427084398670237098368066700150946827562766]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36535290477982, -1736243108587, -1943251241163]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-36535290477982, -1736243108587, -1943251241163]] 
 ![![163, 0, 0], ![0, 163, 0], ![153, 155, 1]] where
  M :=![![![-36535290477982, -1736243108587, -1943251241163], ![-191967856609985, -9122764969124, -10210450518946], ![-106231541815723, -5048373229803, -5650278751950]]]
  hmulB := by decide  
  f := ![![![2813226, -515253, -36430]], ![![-4564216, 2844423, -3570341]], ![![-1999041, 2265017, -3405532]]]
  g := ![![![1599890487239, 1837225148906, -1943251241163], ![8406325599931, 9653356229862, -10210450518946], ![4651908633329, 5341992842469, -5650278751950]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [61, 159, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 162], [0, 1]]
 g := ![![[32, 155], [11, 38], [22], [71], [151], [65, 16], [1]], ![[0, 8], [0, 125], [22], [71], [151], [129, 147], [1]]]
 h' := ![![[4, 162], [144, 127], [49, 110], [139, 115], [118, 87], [110, 71], [102, 4], [0, 1]], ![[0, 1], [0, 36], [0, 53], [110, 48], [140, 76], [68, 92], [118, 159], [4, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143]]
 b := ![[], [20, 153]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [61, 159, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7583, 4496, -7571]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7060, 7227, -7571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2813226, -515253, -36430]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![2813226, -515253, -36430]] 
 ![![163, 0, 0], ![57, 1, 0], ![17, 0, 1]] where
  M :=![![![2813226, -515253, -36430], ![-4564216, 2844423, -3570341], ![-48813781, 7145915, 3874929]]]
  hmulB := by decide  
  f := ![![![-36535290477982, -1736243108587, -1943251241163]], ![![-13953861434693, -663120381341, -742182645799]], ![![-4462156318659, -212052184514, -237334661667]]]
  g := ![![![201239, -515253, -36430], ![-650310, 2844423, -3570341], ![-3202483, 7145915, 3874929]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-36535290477982, -1736243108587, -1943251241163]] ![![2813226, -515253, -36430]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB166I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 165 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 165 (by omega)

def PB166I3 : PrimesBelowBoundCertificateInterval O 137 165 166 where
  m := 5
  g := ![1, 1, 2, 3, 2]
  P := ![139, 149, 151, 157, 163]
  hP := PB166I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
  β := ![I151N1, I157N0, I157N1, I157N2, I163N1]
  Il := ![[], [], [I151N1], [I157N0, I157N1, I157N2], [I163N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
