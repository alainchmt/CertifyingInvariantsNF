
import IdealArithmetic.Examples.NF3_1_981215_1.RI3_1_981215_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![238523348092250234, 15409278533103203, 13390732264085139]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![238523348092250234, 15409278533103203, 13390732264085139]] 
 ![![139, 0, 0], ![55, 1, 0], ![89, 0, 1]] where
  M :=![![![238523348092250234, 15409278533103203, 13390732264085139], ![2542220583907158346, 164234593314793592, 142720599335964955], ![1791569225111389819, 115740406219688814, 100578932913362716]]]
  hmulB := by decide  
  f := ![![![3659002502, -418444202, 106621577]], ![![1597325921, -155182413, 7539981]], ![![1701862766, -226257023, 94476537]]]
  g := ![![![-12955123329007218, 15409278533103203, 13390732264085139], ![-138077808556168131, 164234593314793592, 142720599335964955], ![-97307037023458825, 115740406219688814, 100578932913362716]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 1, 1]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![17, 1, 1]] 
 ![![139, 0, 0], ![88, 1, 0], ![68, 0, 1]] where
  M :=![![![17, 1, 1], ![190, 11, 9], ![105, 10, 7]]]
  hmulB := by decide  
  f := ![![![-13, 3, -2]], ![![-11, 2, -1]], ![![-1, 1, -1]]]
  g := ![![![-1, 1, 1], ![-10, 11, 9], ![-9, 10, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1388252231, 13033193, 166333131]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-1388252231, 13033193, 166333131]] 
 ![![139, 0, 0], ![134, 1, 0], ![138, 0, 1]] where
  M :=![![![-1388252231, 13033193, 166333131], ![31756594828, -2846150831, -189301139], ![-11815309403, 3043030752, -2744983665]]]
  hmulB := by decide  
  f := ![![![-8388686726586802143, -541932734597236857, -470941980738775034]], ![![-8730158323375109941, -563992759278843714, -490112241281207985]], ![![-8781632447723138723, -567318132353095541, -493002005420381891]]]
  g := ![![![-187688289, 13033193, 166333131], ![3160175276, -2846150831, -189301139], ![-293335859, 3043030752, -2744983665]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![238523348092250234, 15409278533103203, 13390732264085139]] ![![17, 1, 1]]
  ![![8388686726586802143, 541932734597236857, 470941980738775034]] where
 M := ![![![8388686726586802143, 541932734597236857, 470941980738775034]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![8388686726586802143, 541932734597236857, 470941980738775034]] ![![-1388252231, 13033193, 166333131]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![278403246, 17985632, 15629595]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![278403246, 17985632, 15629595]] 
 ![![149, 0, 0], ![0, 149, 0], ![15, 13, 1]] where
  M :=![![![278403246, 17985632, 15629595], ![2967267013, 191693787, 166582762], ![2091110542, 135091617, 117395222]]]
  hmulB := by decide  
  f := ![![![-13560, 1039, 331]], ![![62182, -13422, 10767]], ![![5201, -1087, 850]]]
  g := ![![![295029, -1242947, 15629595], ![3144467, -13247531, 166582762], ![2215988, -9335881, 117395222]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [12, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 148], [0, 1]]
 g := ![![[104, 76], [85], [122, 29], [53], [58, 86], [7], [1]], ![[20, 73], [85], [137, 120], [53], [10, 63], [7], [1]]]
 h' := ![![[93, 148], [103, 134], [26, 54], [126, 124], [49, 65], [60, 58], [137, 93], [0, 1]], ![[0, 1], [49, 15], [131, 95], [36, 25], [134, 84], [90, 91], [144, 56], [93, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [5, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [12, 56, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6455, 1323, -1606]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![205, 149, -1606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13560, -1039, -331]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![13560, -1039, -331]] 
 ![![149, 0, 0], ![8, 1, 0], ![19, 0, 1]] where
  M :=![![![13560, -1039, -331], ![-62182, 13422, -10767], ![-169983, 3062, 18286]]]
  hmulB := by decide  
  f := ![![![-278403246, -17985632, -15629595]], ![![-34862369, -2252207, -1957178]], ![![-49535384, -3200125, -2780923]]]
  g := ![![![189, -1039, -331], ![235, 13422, -10767], ![-3637, 3062, 18286]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![278403246, 17985632, 15629595]] ![![13560, -1039, -331]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![198436100263067237, 12819529678888258, 11140228876563477]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![198436100263067237, 12819529678888258, 11140228876563477]] 
 ![![151, 0, 0], ![0, 151, 0], ![63, 126, 1]] where
  M :=![![![198436100263067237, 12819529678888258, 11140228876563477], ![2114964185744735849, 136632629410660718, 118734368714643884], ![1490470485283198256, 96288581544711741, 83675209892782905]]]
  hmulB := by decide  
  f := ![![![-201743154, 29841417, -15485314]], ![![-2987536391, 27148923, 359226215]], ![![-2530516267, 31377350, 292380032]]]
  g := ![![![-3333763701724714, -9210922574623244, 11140228876563477], ![-35531794988594893, -98171508798903766, 118734368714643884], ![-25040183695113409, -69184025595668439, 83675209892782905]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [146, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 150], [0, 1]]
 g := ![![[65, 137], [10, 110], [148, 36], [42], [111, 74], [76], [1]], ![[45, 14], [124, 41], [70, 115], [42], [1, 77], [76], [1]]]
 h' := ![![[23, 150], [50, 99], [136, 84], [44, 6], [102, 93], [103, 15], [5, 23], [0, 1]], ![[0, 1], [62, 52], [105, 67], [31, 145], [127, 58], [146, 136], [81, 128], [23, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [49, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [146, 128, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14985, 16840, -4660]
  a := ![-3, 6, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1845, 4000, -4660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-201743154, 29841417, -15485314]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-201743154, 29841417, -15485314]] 
 ![![151, 0, 0], ![126, 1, 0], ![46, 0, 1]] where
  M :=![![![-201743154, 29841417, -15485314], ![-2987536391, 27148923, 359226215], ![7031447651, -562793719, -137543476]]]
  hmulB := by decide  
  f := ![![![198436100263067237, 12819529678888258, 11140228876563477]], ![![179588826615173561, 11601942840732326, 10082140444779086]], ![![70321397995922458, 4542959912407759, 3947852570958297]]]
  g := ![![![-21519452, 29841417, -15485314], ![-151872229, 27148923, 359226215], ![558082491, -562793719, -137543476]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![198436100263067237, 12819529678888258, 11140228876563477]] ![![-201743154, 29841417, -15485314]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [133, 100, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 114, 122], [130, 42, 35], [0, 1]]
 g := ![![[32, 93, 56], [102, 52], [42, 98, 11], [59, 140, 154], [97, 27, 106], [113, 1], []], ![[76, 122, 73, 143], [45, 111], [54, 71, 113, 86], [12, 50, 27, 33], [155, 48, 141, 51], [134, 37], [135, 126]], ![[84, 80, 87, 19], [149, 9], [151, 144, 0, 127], [57, 28, 137, 82], [51, 92, 94, 82], [32, 122], [65, 126]]]
 h' := ![![[140, 114, 122], [53, 128, 29], [66, 45, 44], [3, 73, 47], [130, 19, 25], [43, 28, 109], [0, 0, 1], [0, 1]], ![[130, 42, 35], [52, 147, 35], [89, 72, 116], [89, 86, 47], [112, 70, 71], [49, 32, 144], [75, 92, 42], [140, 114, 122]], ![[0, 1], [21, 39, 93], [29, 40, 154], [111, 155, 63], [8, 68, 61], [100, 97, 61], [91, 65, 114], [130, 42, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 153], []]
 b := ![[], [82, 1, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [133, 100, 44, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-269920837, -62404674, -136142079]
  a := ![1, -66, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1719241, -397482, -867147]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3990228, 535043, -227976]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-3990228, 535043, -227976]] 
 ![![163, 0, 0], ![0, 163, 0], ![67, 36, 1]] where
  M :=![![![-3990228, 535043, -227976], ![-44078459, -333315, 6341425], ![121799149, -9146931, -3236506]]]
  hmulB := by decide  
  f := ![![![362474557755, 23416874978, 20349369545]], ![![3863312708117, 249580856784, 216886885668]], ![![1018942516575, 65826549781, 57203567454]]]
  g := ![![![69228, 53633, -227976], ![-2877018, -1402605, 6341425], ![2077577, 658695, -3236506]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [35, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 162], [0, 1]]
 g := ![![[34, 14], [79, 33], [118], [96], [56], [44, 119], [1]], ![[0, 149], [92, 130], [118], [96], [56], [81, 44], [1]]]
 h' := ![![[114, 162], [6, 60], [14, 14], [45, 97], [109, 111], [90, 120], [128, 114], [0, 1]], ![[0, 1], [0, 103], [143, 149], [19, 66], [49, 52], [78, 43], [84, 49], [114, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [111, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [35, 49, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2354, 15186, -10309]
  a := ![3, -7, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4223, 2370, -10309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![362474557755, 23416874978, 20349369545]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![362474557755, 23416874978, 20349369545]] 
 ![![163, 0, 0], ![95, 1, 0], ![13, 0, 1]] where
  M :=![![![362474557755, 23416874978, 20349369545], ![3863312708117, 249580856784, 216886885668], ![2722577339928, 175886146553, 152845851439]]]
  hmulB := by decide  
  f := ![![![-3990228, 535043, -227976]], ![![-2596013, 309790, -93965]], ![![428995, -13444, -38038]]]
  g := ![![![-13047057480, 23416874978, 20349369545], ![-139057657669, 249580856784, 216886885668], ![-97997562278, 175886146553, 152845851439]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-3990228, 535043, -227976]] ![![362474557755, 23416874978, 20349369545]]
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
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![111667, 7214, 6269]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![111667, 7214, 6269]] 
 ![![167, 0, 0], ![90, 1, 0], ![74, 0, 1]] where
  M :=![![![111667, 7214, 6269], ![1190165, 76888, 66816], ![838740, 54185, 47087]]]
  hmulB := by decide  
  f := ![![![296, 147, -248]], ![![-125, 97, -121]], ![![427, 29, -98]]]
  g := ![![![-5997, 7214, 6269], ![-63917, 76888, 66816], ![-45044, 54185, 47087]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5661, -331, -284]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![5661, -331, -284]] 
 ![![167, 0, 0], ![110, 1, 0], ![130, 0, 1]] where
  M :=![![![5661, -331, -284], ![-53913, 7224, -3073], ![-38797, -2417, 8595]]]
  hmulB := by decide  
  f := ![![![54662839, 3531373, 3068779]], ![![39494118, 2551431, 2217205]], ![![45010457, 2907802, 2526893]]]
  g := ![![![473, -331, -284], ![-2689, 7224, -3073], ![-5331, -2417, 8595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-232, -15, -13]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-232, -15, -13]] 
 ![![167, 0, 0], ![133, 1, 0], ![147, 0, 1]] where
  M :=![![![-232, -15, -13], ![-2468, -160, -139], ![-1747, -112, -98]]]
  hmulB := by decide  
  f := ![![![-112, 14, -5]], ![![-95, 11, -3]], ![![-80, 11, -5]]]
  g := ![![![22, -15, -13], ![235, -160, -139], ![165, -112, -98]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![111667, 7214, 6269]] ![![5661, -331, -284]]
  ![![112, -14, 5]] where
 M := ![![![112, -14, 5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![112, -14, 5]] ![![-232, -15, -13]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-884590, -57147, -49661]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-884590, -57147, -49661]] 
 ![![173, 0, 0], ![39, 1, 0], ![24, 0, 1]] where
  M :=![![![-884590, -57147, -49661], ![-9428104, -609082, -529295], ![-6644231, -429236, -373008]]]
  hmulB := by decide  
  f := ![![![9964, -820, -163]], ![![2071, -133, -87]], ![![558, -89, 52]]]
  g := ![![![14659, -57147, -49661], ![156238, -609082, -529295], ![110105, -429236, -373008]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2468, 1, -330]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![2468, 1, -330]] 
 ![![173, 0, 0], ![66, 1, 0], ![42, 0, 1]] where
  M :=![![![2468, 1, -330], ![-63031, 5441, 671], ![28571, -6279, 5106]]]
  hmulB := by decide  
  f := ![![![-31994955, -2066964, -1796201]], ![![-14177309, -915894, -795916]], ![![-9156676, -591547, -514057]]]
  g := ![![![94, 1, -330], ![-2603, 5441, 671], ![1321, -6279, 5106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, 1, 1]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![18, 1, 1]] 
 ![![173, 0, 0], ![67, 1, 0], ![124, 0, 1]] where
  M :=![![![18, 1, 1], ![190, 12, 9], ![105, 10, 8]]]
  hmulB := by decide  
  f := ![![![6, 2, -3]], ![![-1, 1, -1]], ![![8, 1, -2]]]
  g := ![![![-1, 1, 1], ![-10, 12, 9], ![-9, 10, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-884590, -57147, -49661]] ![![2468, 1, -330]]
  ![![6, 2, -3]] where
 M := ![![![6, 2, -3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![6, 2, -3]] ![![18, 1, 1]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2204489666, -142416227, -123760341]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-2204489666, -142416227, -123760341]] 
 ![![179, 0, 0], ![0, 179, 0], ![155, 26, 1]] where
  M :=![![![-2204489666, -142416227, -123760341], ![-23495808904, -1517895278, -1319057815], ![-16558110031, -1069700436, -929574484]]]
  hmulB := by decide  
  f := ![![![10172, -2552, 2267]], ![![435549, -17887, -32606]], ![![68260, -4439, -2789]]]
  g := ![![![94851191, 17180741, -123760341], ![1010939399, 183115128, -1319057815], ![712435391, 129046012, -929574484]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [135, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 178], [0, 1]]
 g := ![![[127, 61], [62, 3], [83], [101], [6, 52], [101, 89], [1]], ![[0, 118], [0, 176], [83], [101], [65, 127], [171, 90], [1]]]
 h' := ![![[39, 178], [43, 132], [154, 19], [34, 158], [85, 82], [148, 125], [44, 39], [0, 1]], ![[0, 1], [0, 47], [0, 160], [110, 21], [61, 97], [11, 54], [133, 140], [39, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [40, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [135, 140, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6662, 987, -2530]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2228, 373, -2530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10172, -2552, 2267]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![10172, -2552, 2267]] 
 ![![179, 0, 0], ![74, 1, 0], ![84, 0, 1]] where
  M :=![![![10172, -2552, 2267], ![435549, -17887, -32606], ![-682394, 66041, -2860]]]
  hmulB := by decide  
  f := ![![![-2204489666, -142416227, -123760341]], ![![-1042614772, -67355844, -58532531]], ![![-1127012525, -72808176, -63270632]]]
  g := ![![![48, -2552, 2267], ![25129, -17887, -32606], ![-29772, 66041, -2860]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-2204489666, -142416227, -123760341]] ![![10172, -2552, 2267]]
  ![![179, 0, 0]] where
 M := ![![![179, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [177, 161, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 130, 25], [35, 50, 156], [0, 1]]
 g := ![![[81], [127, 132], [0, 153, 70], [100, 133], [5, 102, 177], [29, 178, 1], []], ![[103, 6, 51, 73], [134, 121], [70, 128, 158, 142], [67, 75], [8, 83, 135, 34], [146, 84, 50, 55], [100, 82]], ![[7, 129, 114, 108], [172, 102], [178, 135, 72, 44], [148, 100], [106, 149, 112, 152], [141, 33, 154, 135], [150, 82]]]
 h' := ![![[143, 130, 25], [146, 172], [0, 53, 133], [76, 173, 147], [20, 27, 26], [116, 25, 38], [0, 0, 1], [0, 1]], ![[35, 50, 156], [126, 97, 137], [155, 146, 11], [129, 156, 91], [59, 104, 165], [96, 82, 172], [34, 50, 50], [143, 130, 25]], ![[0, 1], [12, 93, 44], [49, 163, 37], [10, 33, 124], [88, 50, 171], [113, 74, 152], [15, 131, 130], [35, 50, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 57], []]
 b := ![[], [67, 166, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [177, 161, 3, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10511756, 2231549, 458473]
  a := ![-1, 23, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![58076, 12329, 2533]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1005887630383, -64983167449, -56470664419]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-1005887630383, -64983167449, -56470664419]] 
 ![![191, 0, 0], ![0, 191, 0], ![84, 109, 1]] where
  M :=![![![-1005887630383, -64983167449, -56470664419], ![-10720913736580, -692601152959, -601873513101], ![-7555307842725, -488094116920, -424155980133]]]
  hmulB := by decide  
  f := ![![![772803, -71093, -2008]], ![![-312435, 577596, -778007]], ![![91382, 301507, -440002]]]
  g := ![![![19568838643, 31886488242, -56470664419], ![208567860544, 339851370550, -601873513101], ![146983217217, 239502134647, -424155980133]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [189, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 190], [0, 1]]
 g := ![![[40, 15], [189, 162], [59, 25], [8, 13], [178, 149], [58, 97], [1]], ![[94, 176], [161, 29], [149, 166], [93, 178], [65, 42], [178, 94], [1]]]
 h' := ![![[80, 190], [187, 145], [118, 60], [16, 5], [165, 108], [116, 63], [2, 80], [0, 1]], ![[0, 1], [136, 46], [143, 131], [34, 186], [19, 83], [190, 128], [99, 111], [80, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [119, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [189, 111, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7500, 2410, -2545]
  a := ![1, -1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1080, 1465, -2545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![772803, -71093, -2008]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![772803, -71093, -2008]] 
 ![![191, 0, 0], ![140, 1, 0], ![142, 0, 1]] where
  M :=![![![772803, -71093, -2008], ![-312435, 577596, -778007], ![-13406075, 601685, 931053]]]
  hmulB := by decide  
  f := ![![![-1005887630383, -64983167449, -56470664419]], ![![-793430272200, -51257825109, -44543280271]], ![![-787389274121, -50867559658, -44204137841]]]
  g := ![![![57649, -71093, -2008], ![153409, 577596, -778007], ![-1203411, 601685, 931053]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-1005887630383, -64983167449, -56470664419]] ![![772803, -71093, -2008]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [49, 64, 180, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [166, 103, 12], [40, 89, 181], [0, 1]]
 g := ![![[36, 135, 4], [184, 46], [161, 95], [95, 28], [128, 157], [147, 169], [1]], ![[17, 186, 44, 100], [1, 187], [146, 65], [108, 98], [99, 16], [72, 9], [42, 133, 182, 184]], ![[73, 91, 59, 7], [52, 172], [88, 129], [130, 145], [32, 145], [75, 63], [4, 135, 158, 9]]]
 h' := ![![[166, 103, 12], [181, 69, 2], [133, 16, 168], [63, 102, 148], [47, 105, 75], [23, 163, 93], [144, 129, 13], [0, 1]], ![[40, 89, 181], [15, 14, 41], [8, 83, 90], [139, 162, 114], [151, 70, 22], [131, 107, 4], [68, 89, 3], [166, 103, 12]], ![[0, 1], [168, 110, 150], [20, 94, 128], [47, 122, 124], [137, 18, 96], [57, 116, 96], [114, 168, 177], [40, 89, 181]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 165], []]
 b := ![[], [31, 39, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [49, 64, 180, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32742643, -1306031, 643269]
  a := ![-2, 7, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![169651, -6767, 3333]
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



lemma PB281I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB281I3 : PrimesBelowBoundCertificateInterval O 137 193 281 where
  m := 11
  g := ![3, 2, 2, 1, 2, 3, 3, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB281I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
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
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
    · exact ![173, 173, 173]
    · exact ![32041, 179]
    · exact ![5929741]
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
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I139N2, I149N1, I151N1, I163N1, I167N0, I167N1, I167N2, I173N0, I173N1, I173N2, I179N1, I191N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N1], [], [I163N1], [I167N0, I167N1, I167N2], [I173N0, I173N1, I173N2], [I179N1], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
