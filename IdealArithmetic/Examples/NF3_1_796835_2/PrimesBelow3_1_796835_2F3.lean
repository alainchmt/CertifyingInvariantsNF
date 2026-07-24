
import IdealArithmetic.Examples.NF3_1_796835_2.RI3_1_796835_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [110, 45, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 113, 103], [98, 25, 36], [0, 1]]
 g := ![![[97, 73, 127], [51, 81, 49], [126, 86], [28, 27, 89], [79, 83], [131, 1], []], ![[14, 30, 24, 68], [55, 74, 104, 15], [85, 46], [86, 77, 99, 8], [88, 31], [51, 69], [122, 45]], ![[122, 76, 5, 63], [18, 15, 11, 137], [77, 9], [26, 117, 103, 37], [17, 34], [73, 120], [50, 45]]]
 h' := ![![[33, 113, 103], [89, 105, 31], [107, 4, 7], [117, 92, 15], [98, 29, 111], [46, 111, 19], [0, 0, 1], [0, 1]], ![[98, 25, 36], [68, 43, 53], [102, 11, 31], [0, 138, 121], [74, 37, 63], [21, 87, 93], [40, 76, 25], [33, 113, 103]], ![[0, 1], [132, 130, 55], [37, 124, 101], [81, 48, 3], [62, 73, 104], [79, 80, 27], [73, 63, 113], [98, 25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 72], []]
 b := ![[], [95, 42, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [110, 45, 8, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10215388, -2719674, -1001634]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73492, -19566, -7206]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![10, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![10, 1, 0]] 
 ![![149, 0, 0], ![10, 1, 0], ![51, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![10, 1, 0], ![3, 14, 9], ![-141, -20, 7]]]
  hmulB := by decide  
  f := ![![![-5594, -26247, -16875], ![-447, 279375, 0]], ![![-375, -1750, -1125], ![1, 18625, 0]], ![![-1916, -8984, -5776], ![-134, 95625, 0]]]
  g := ![![![1, 0, 0], ![-10, 149, 0], ![-51, 0, 149]], ![![0, 1, 0], ![-4, 14, 9], ![-2, -20, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![65, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![65, 1, 0]] 
 ![![149, 0, 0], ![65, 1, 0], ![98, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![65, 1, 0], ![3, 69, 9], ![-141, -20, 62]]]
  hmulB := by decide  
  f := ![![![31335, 920878, 120132], ![19966, -1988852, 0]], ![![13631, 401659, 52398], ![8792, -867478, 0]], ![![20600, 605678, 79013], ![13154, -1308104, 0]]]
  g := ![![![1, 0, 0], ![-65, 149, 0], ![-98, 0, 149]], ![![0, 1, 0], ![-36, 69, 9], ![-33, -20, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![73, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![73, 1, 0]] 
 ![![149, 0, 0], ![73, 1, 0], ![38, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![73, 1, 0], ![3, 77, 9], ![-141, -20, 70]]]
  hmulB := by decide  
  f := ![![![-7219, -248984, -29106], ![-5066, 481866, 0]], ![![-3511, -121951, -14256], ![-2532, 236016, 0]], ![![-1894, -63500, -7423], ![-1184, 122892, 0]]]
  g := ![![![1, 0, 0], ![-73, 149, 0], ![-38, 0, 149]], ![![0, 1, 0], ![-40, 77, 9], ![-9, -20, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![10, 1, 0]] ![![149, 0, 0], ![65, 1, 0]]
  ![![149, 0, 0], ![56, -74, 1]] where
 M := ![![![22201, 0, 0], ![9685, 149, 0]], ![![1490, 149, 0], ![653, 79, 9]]]
 hmul := by decide  
 g := ![![![![93, 74, -1], ![149, 0, 0]], ![![9, 75, -1], ![149, 0, 0]]], ![![![-46, 75, -1], ![149, 0, 0]], ![![1, 5, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![56, -74, 1]] ![![149, 0, 0], ![73, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![10877, 149, 0]], ![![8344, -11026, 149], ![3725, -5662, -596]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![73, 1, 0]]], ![![![56, -74, 1]], ![![25, -38, -4]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-186136804813762212574379, 2704263985342832842078, -7946204241384852283830]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-186136804813762212574379, 2704263985342832842078, -7946204241384852283830]] 
 ![![151, 0, 0], ![0, 151, 0], ![35, 87, 1]] where
  M :=![![![-186136804813762212574379, 2704263985342832842078, -7946204241384852283830], ![1128527589991292670546264, -16395664044693835529467, 48176988592240052430192], ![-1199760258795979215967488, 17430558465607013712910, -51217920424863369991673]]]
  hmulB := by decide  
  f := ![![![169266013579, 16077292906, -11138030466]], ![![1618694174424, 456335794523, 178109727552]], ![![949248928559, 265182886035, 102167112013]]]
  g := ![![![609141348574222631521, 4596185648912748222088, -7946204241384852283830], ![-3693159011504034202056, -27866183255427671503021, 48176988592240052430192], ![3926271232279726713517, 29625096923369007966811, -51217920424863369991673]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [39, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [150, 150], [0, 1]]
 g := ![![[31, 31], [73, 95], [4, 145], [39], [27, 40], [1], [1]], ![[0, 120], [129, 56], [10, 6], [39], [138, 111], [1], [1]]]
 h' := ![![[150, 150], [22, 22], [146, 104], [5, 30], [4, 103], [123, 77], [112, 150], [0, 1]], ![[0, 1], [0, 129], [42, 47], [126, 121], [52, 48], [46, 74], [113, 1], [150, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [38, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [39, 1, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-789, -3976, -3090]
  a := ![4, 5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![711, 1754, -3090]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-169266013579, -16077292906, 11138030466]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-169266013579, -16077292906, 11138030466]] 
 ![![151, 0, 0], ![126, 1, 0], ![93, 0, 1]] where
  M :=![![![-169266013579, -16077292906, 11138030466], ![-1618694174424, -456335794523, -178109727552], ![3414115437744, 221303583926, -321518683249]]]
  hmulB := by decide  
  f := ![![![186136804813762212574379, -2704263985342832842078, 7946204241384852283830]], ![![147845760374455272276990, -2147957603367570215711, 6311554608094379704188]], ![![122585980837588509836985, -1780974232466824291564, 5233211356779169750913]]]
  g := ![![![5434675889, -16077292906, 11138030466], ![479760401310, -456335794523, -178109727552], ![35967558975, 221303583926, -321518683249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-186136804813762212574379, 2704263985342832842078, -7946204241384852283830]] ![![-169266013579, -16077292906, 11138030466]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1807732859686575, 594731906373465, 278960520718984]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![1807732859686575, 594731906373465, 278960520718984]] 
 ![![157, 0, 0], ![0, 157, 0], ![40, 120, 1]] where
  M :=![![![1807732859686575, 594731906373465, 278960520718984], ![-37549237702256349, -1392549929199245, 4515705595204233], ![-55124265164603213, -14405282813940156, -4997752232375532]]]
  hmulB := by decide  
  f := ![![![-458660100132222014654707966584, 6663582688777302125802223332, -19580258921234023111935266525]], ![![2780807255960329165160279250021, -40400590952432343912793742756, 118713020962697788468025809563]], ![![1989771559757617294603679906989, -28908133313536490566954059015, 84943604911197657239926156990]]]
  g := ![![![-59558522096005, -209430131082195, 278960520718984], ![-1389665359939017, -3460364467221065, 4515705595204233], ![922202701467631, 3728184618287412, -4997752232375532]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [63, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 156], [0, 1]]
 g := ![![[54, 141], [115], [89, 111], [134, 115], [147, 13], [35], [1]], ![[7, 16], [115], [52, 46], [148, 42], [38, 144], [35], [1]]]
 h' := ![![[52, 156], [118, 45], [45, 30], [36, 41], [2, 30], [37, 135], [94, 52], [0, 1]], ![[0, 1], [103, 112], [35, 127], [127, 116], [149, 127], [149, 22], [129, 105], [52, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [41, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [63, 105, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-623509, -476524, -318688]
  a := ![-65, -65, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![77223, 240548, -318688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-458660100132222014654707966584, 6663582688777302125802223332, -19580258921234023111935266525]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-458660100132222014654707966584, 6663582688777302125802223332, -19580258921234023111935266525]] 
 ![![157, 0, 0], ![22, 1, 0], ![24, 0, 1]] where
  M :=![![![-458660100132222014654707966584, 6663582688777302125802223332, -19580258921234023111935266525], ![2780807255960329165160279250021, -40400590952432343912793742756, 118713020962697788468025809563], ![-2956331828004703980267445941887, 42950676515560165491372932085, -126206187616341505017279839130]]]
  hmulB := by decide  
  f := ![![![1807732859686575, 594731906373465, 278960520718984]], ![![14145765674193, 74468484146605, 67852465293133]], ![![-74768640332009, -838962171828, 10810829712612]]]
  g := ![![![-861991752711503864559939384, 6663582688777302125802223332, -19580258921234023111935266525], ![5226164037000597503242816313, -40400590952432343912793742756, 118713020962697788468025809563], ![-5556039544935232488298944641, 42950676515560165491372932085, -126206187616341505017279839130]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![1807732859686575, 594731906373465, 278960520718984]] ![![-458660100132222014654707966584, 6663582688777302125802223332, -19580258921234023111935266525]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![29, -4, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![29, -4, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![29, 159, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![29, -4, 1], ![-153, -7, -39], ![667, 71, 23]]]
  hmulB := by decide  
  f := ![![![-28, 4, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -159, 163]], ![![0, -1, 1], ![6, 38, -39], ![0, -22, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [45, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 162], [0, 1]]
 g := ![![[141, 47], [41, 61], [58], [91], [135], [159, 144], [1]], ![[53, 116], [121, 102], [58], [91], [135], [94, 19], [1]]]
 h' := ![![[12, 162], [111, 84], [113, 77], [21, 59], [82, 108], [17, 61], [118, 12], [0, 1]], ![[0, 1], [141, 79], [59, 86], [77, 104], [74, 55], [97, 102], [99, 151], [12, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145]]
 b := ![[], [54, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [45, 151, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6314, -10185, -9475]
  a := ![-6, -8, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1647, 9180, -9475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![39, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![39, 1, 0]] 
 ![![163, 0, 0], ![39, 1, 0], ![140, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![39, 1, 0], ![3, 43, 9], ![-141, -20, 36]]]
  hmulB := by decide  
  f := ![![![-19316, -298639, -62514], ![-6357, 1132198, 0]], ![![-4632, -71414, -14949], ![-1466, 270743, 0]], ![![-16600, -256500, -53693], ![-5420, 972440, 0]]]
  g := ![![![1, 0, 0], ![-39, 163, 0], ![-140, 0, 163]], ![![0, 1, 0], ![-18, 43, 9], ![-27, -20, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![29, -4, 1]] ![![163, 0, 0], ![39, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![6357, 163, 0]], ![![4727, -652, 163], ![978, -163, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![39, 1, 0]]], ![![![29, -4, 1]], ![![6, -1, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [101, 166, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 32, 83], [25, 134, 84], [0, 1]]
 g := ![![[56, 101, 11], [106, 26, 154], [5, 36, 141], [141, 42], [164, 24], [39, 47, 1], []], ![[128, 123, 70, 10], [151, 61, 149, 111], [75, 114, 16, 164], [88, 50], [130, 132], [77, 103, 111, 40], [105, 42]], ![[92, 121, 131, 154], [109, 6, 27, 27], [144, 64, 52, 116], [146, 157], [146, 56], [72, 44, 112, 11], [104, 42]]]
 h' := ![![[22, 32, 83], [149, 1, 126], [163, 2, 34], [31, 5, 59], [54, 4, 84], [69, 135, 109], [0, 0, 1], [0, 1]], ![[25, 134, 84], [137, 31, 100], [113, 130, 46], [27, 137, 138], [8, 16, 65], [46, 111, 93], [66, 110, 134], [22, 32, 83]], ![[0, 1], [71, 135, 108], [164, 35, 87], [125, 25, 137], [141, 147, 18], [109, 88, 132], [141, 57, 32], [25, 134, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156, 95], []]
 b := ![[], [5, 156, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [101, 166, 120, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10917458, -3387929, -1461417]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65374, -20287, -8751]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-5, -40, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-5, -40, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![168, 133, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-5, -40, 1], ![-261, -185, -363], ![5743, 791, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-168, -133, 173]], ![![-1, -1, 1], ![351, 278, -363], ![-61, -70, 97]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [123, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 172], [0, 1]]
 g := ![![[119, 24], [96], [4, 136], [17, 52], [160], [144, 126], [1]], ![[21, 149], [96], [83, 37], [93, 121], [160], [62, 47], [1]]]
 h' := ![![[68, 172], [166, 71], [27, 31], [158, 89], [73, 15], [107, 81], [50, 68], [0, 1]], ![[0, 1], [150, 102], [59, 142], [155, 84], [55, 158], [79, 92], [3, 105], [68, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [135, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [123, 105, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-558296, -423531, -269529]
  a := ![42, 62, 125]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![258512, 204762, -269529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![17, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![17, 1, 0]] 
 ![![173, 0, 0], ![17, 1, 0], ![76, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![17, 1, 0], ![3, 21, 9], ![-141, -20, 14]]]
  hmulB := by decide  
  f := ![![![22207, 157566, 67536], ![3114, -1298192, 0]], ![![2177, 15475, 6633], ![347, -127501, 0]], ![![9743, 69219, 29669], ![1497, -570304, 0]]]
  g := ![![![1, 0, 0], ![-17, 173, 0], ![-76, 0, 173]], ![![0, 1, 0], ![-6, 21, 9], ![-5, -20, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-5, -40, 1]] ![![173, 0, 0], ![17, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![2941, 173, 0]], ![![-865, -6920, 173], ![-346, -865, -346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![17, 1, 0]]], ![![![-5, -40, 1]], ![![-2, -5, -2]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![34, 30, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![34, 30, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![34, 30, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![34, 30, 1], ![-51, 134, 267], ![-4127, -609, -74]]]
  hmulB := by decide  
  f := ![![![-33, -30, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -30, 179]], ![![0, 0, 1], ![-51, -44, 267], ![-9, 9, -74]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [27, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 178], [0, 1]]
 g := ![![[136, 126], [128, 87], [76], [146], [163, 65], [97, 51], [1]], ![[0, 53], [0, 92], [76], [146], [90, 114], [59, 128], [1]]]
 h' := ![![[87, 178], [124, 157], [118, 83], [102, 104], [74, 135], [66, 94], [152, 87], [0, 1]], ![[0, 1], [0, 22], [0, 96], [21, 75], [5, 44], [10, 85], [24, 92], [87, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [55, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [27, 92, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2586, -1113, -234]
  a := ![2, 4, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30, 33, -234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-88, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-88, 1, 0]] 
 ![![179, 0, 0], ![91, 1, 0], ![74, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-88, 1, 0], ![3, -84, 9], ![-141, -20, -91]]]
  hmulB := by decide  
  f := ![![![20681, -776080, 83160], ![-14320, -1653960, 0]], ![![10484, -394507, 42273], ![-7338, -840763, 0]], ![![8590, -320838, 34379], ![-5838, -683760, 0]]]
  g := ![![![1, 0, 0], ![-91, 179, 0], ![-74, 0, 179]], ![![-1, 1, 0], ![39, -84, 9], ![47, -20, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![34, 30, 1]] ![![179, 0, 0], ![-88, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-15752, 179, 0]], ![![6086, 5370, 179], ![-3043, -2506, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-88, 1, 0]]], ![![![34, 30, 1]], ![![-17, -14, 1]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [125, 17, 153, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 94, 23], [130, 86, 158], [0, 1]]
 g := ![![[121, 149, 176], [158, 117], [154, 8, 52], [25, 177], [170, 149, 161], [43, 28, 1], []], ![[64, 76, 24, 107], [38, 60], [63, 31, 137, 146], [72, 13], [38, 108, 134, 35], [47, 131, 27, 149], [131, 167]], ![[160, 78, 74, 123], [128, 172], [81, 117, 95, 10], [124, 119], [100, 46, 4, 57], [151, 65, 61, 35], [177, 167]]]
 h' := ![![[79, 94, 23], [93, 143, 151], [117, 121, 29], [32, 0, 41], [108, 153, 143], [55, 113, 60], [0, 0, 1], [0, 1]], ![[130, 86, 158], [108, 121, 166], [141, 3, 28], [114, 39, 87], [173, 91, 70], [52, 159, 157], [2, 76, 86], [79, 94, 23]], ![[0, 1], [44, 98, 45], [72, 57, 124], [111, 142, 53], [81, 118, 149], [76, 90, 145], [24, 105, 94], [130, 86, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 132], []]
 b := ![[], [96, 180, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [125, 17, 153, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38530013, 8555508, 2426124]
  a := ![8, 11, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![212873, 47268, 13404]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [167, 182, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 165, 163], [11, 25, 28], [0, 1]]
 g := ![![[118, 22, 170], [17, 141, 50], [70, 143, 77], [11, 142, 118], [46, 110, 117], [111, 169, 1], []], ![[11, 86, 79, 64], [136, 96, 73, 45], [125, 35, 44, 90], [50, 190, 117, 133], [101, 126, 162, 78], [75, 90, 40, 72], [61, 20]], ![[16, 63, 119, 140], [177, 97, 134, 122], [10, 134, 178, 164], [80, 52, 185, 157], [187, 142, 55, 55], [42, 54, 101, 19], [5, 20]]]
 h' := ![![[158, 165, 163], [26, 92, 172], [152, 32, 94], [73, 114, 29], [149, 98, 51], [181, 89, 58], [0, 0, 1], [0, 1]], ![[11, 25, 28], [53, 79, 5], [137, 112, 117], [60, 50, 16], [103, 118, 59], [158, 85, 104], [70, 71, 25], [158, 165, 163]], ![[0, 1], [88, 20, 14], [47, 47, 171], [103, 27, 146], [148, 166, 81], [49, 17, 29], [50, 120, 165], [11, 25, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166, 96], []]
 b := ![[], [186, 80, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [167, 182, 22, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3323018, -861410, -299870]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17398, -4510, -1570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![87, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![87, 1, 0]] 
 ![![193, 0, 0], ![87, 1, 0], ![150, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![87, 1, 0], ![3, 91, 9], ![-141, -20, 84]]]
  hmulB := by decide  
  f := ![![![-17444, -684807, -67734], ![-11387, 1452518, 0]], ![![-7914, -308646, -30528], ![-5017, 654656, 0]], ![![-13608, -532234, -52643], ![-8738, 1128900, 0]]]
  g := ![![![1, 0, 0], ![-87, 193, 0], ![-150, 0, 193]], ![![0, 1, 0], ![-48, 91, 9], ![-57, -20, 84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-66, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-66, 1, 0]] 
 ![![193, 0, 0], ![127, 1, 0], ![189, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-66, 1, 0], ![3, -62, 9], ![-141, -20, -69]]]
  hmulB := by decide  
  f := ![![![-3281, 80095, -11628], ![1737, 249356, 0]], ![![-2153, 52694, -7650], ![1159, 164050, 0]], ![![-3213, 78435, -11387], ![1701, 244188, 0]]]
  g := ![![![1, 0, 0], ![-127, 193, 0], ![-189, 0, 193]], ![![-1, 1, 0], ![32, -62, 9], ![80, -20, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-22, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-22, 1, 0]] 
 ![![193, 0, 0], ![171, 1, 0], ![85, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-22, 1, 0], ![3, -18, 9], ![-141, -20, -25]]]
  hmulB := by decide  
  f := ![![![17499, -106691, 53352], ![-2509, -1144104, 0]], ![![15515, -94525, 47268], ![-2122, -1013636, 0]], ![![7723, -46989, 23497], ![-963, -503880, 0]]]
  g := ![![![1, 0, 0], ![-171, 193, 0], ![-85, 0, 193]], ![![-1, 1, 0], ![12, -18, 9], ![28, -20, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![87, 1, 0]] ![![193, 0, 0], ![-66, 1, 0]]
  ![![193, 0, 0], ![70, -83, 1]] where
 M := ![![![37249, 0, 0], ![-12738, 193, 0]], ![![16791, 193, 0], ![-5739, 25, 9]]]
 hmul := by decide  
 g := ![![![![123, 83, -1], ![193, 0, 0]], ![![-66, 1, 0], ![0, 0, 0]]], ![![![17, 84, -1], ![193, 0, 0]], ![![-33, 4, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![70, -83, 1]] ![![193, 0, 0], ![-22, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-4246, 193, 0]], ![![13510, -16019, 193], ![-1930, 1544, -772]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-22, 1, 0]]], ![![![70, -83, 1]], ![![-10, 8, -4]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB253I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB253I3 : PrimesBelowBoundCertificateInterval O 137 193 253 where
  m := 11
  g := ![1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB253I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![6967871]
    · exact ![193, 193, 193]
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
      exact NI149N1
      exact NI149N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I149N0, I149N1, I149N2, I151N1, I157N1, I163N1, I173N1, I179N1, I193N0, I193N1, I193N2]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N1], [I157N1], [I163N1], [], [I173N1], [I179N1], [], [], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
