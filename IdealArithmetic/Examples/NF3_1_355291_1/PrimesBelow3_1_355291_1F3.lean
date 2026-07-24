
import IdealArithmetic.Examples.NF3_1_355291_1.RI3_1_355291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22988098247804859, 5103277942594734, -2199064655095444]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-22988098247804859, 5103277942594734, -2199064655095444]] 
 ![![139, 0, 0], ![0, 139, 0], ![22, 69, 1]] where
  M :=![![![-22988098247804859, 5103277942594734, -2199064655095444], ![281480275852216832, -62487643281638945, 26926686977781362], ![-371739300799909120, 82524833229687402, -35560956303857583]]]
  hmulB := by decide  
  f := ![![![-283054449, -14585406, 6459848]], ![![-826860544, -168239903, -76258450]], ![![-447773410, -87535179, -38591473]]]
  g := ![![![182671396865431, 1128336252835830, -2199064655095444], ![-2236739839273188, -13816036293155057, 26926686977781362], ![2953969337301854, 18246264879106911, -35560956303857583]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [79, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 138], [0, 1]]
 g := ![![[3, 44], [102, 106], [38], [6, 118], [51], [13], [1]], ![[0, 95], [0, 33], [38], [118, 21], [51], [13], [1]]]
 h' := ![![[41, 138], [4, 105], [108, 55], [82, 90], [39, 102], [71, 32], [60, 41], [0, 1]], ![[0, 1], [0, 34], [0, 84], [19, 49], [51, 37], [132, 107], [73, 98], [41, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [104, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [79, 98, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2993, -2633, 679]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-129, -356, 679]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-283054449, -14585406, 6459848]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-283054449, -14585406, 6459848]] 
 ![![139, 0, 0], ![69, 1, 0], ![104, 0, 1]] where
  M :=![![![-283054449, -14585406, 6459848], ![-826860544, -168239903, -76258450], ![1040071424, -237957642, -244498353]]]
  hmulB := by decide  
  f := ![![![-22988098247804859, 5103277942594734, -2199064655095444]], ![![-9386320167239701, 2083730465880559, -897904850530966]], ![![-19874111644400104, 4411983735680142, -1901177557077581]]]
  g := ![![![370607, -14585406, 6459848], ![134622817, -168239903, -76258450], ![308539406, -237957642, -244498353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-22988098247804859, 5103277942594734, -2199064655095444]] ![![-283054449, -14585406, 6459848]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-443470260871558990057639, 98448857148009999216482, -42422812263808099040880]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-443470260871558990057639, 98448857148009999216482, -42422812263808099040880]] 
 ![![149, 0, 0], ![0, 149, 0], ![14, 138, 1]] where
  M :=![![![-443470260871558990057639, 98448857148009999216482, -42422812263808099040880], ![5430119969767436677232640, -1205467767217478077156765, 519450750980837598351854], ![-7171333745177843222477056, 1592011175793807179871862, -686017016236640478804911]]]
  hmulB := by decide  
  f := ![![![377436988317, 86481650842, 42143298628]], ![![-5394342224384, 581568320699, 773944750406]], ![![-5071134917186, 549749999624, 729865065825]]]
  g := ![![![1009725575984928835669, 39951657379553876958778, -42422812263808099040880], ![-12363694925934830199284, -489192425520624608387333, 519450750980837598351854], ![16328218000906868998602, 646056103466108679563420, -686017016236640478804911]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [124, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 148], [0, 1]]
 g := ![![[27, 143], [68], [141, 53], [73], [6, 112], [132], [1]], ![[0, 6], [68], [7, 96], [73], [63, 37], [132], [1]]]
 h' := ![![[79, 148], [129, 21], [98, 51], [38, 84], [1, 64], [51, 74], [25, 79], [0, 1]], ![[0, 1], [0, 128], [104, 98], [118, 65], [140, 85], [86, 75], [8, 70], [79, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [132, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [124, 70, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1353, -3077, 2298]
  a := ![-1, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-225, -2149, 2298]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![377436988317, 86481650842, 42143298628]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![377436988317, 86481650842, 42143298628]] 
 ![![149, 0, 0], ![73, 1, 0], ![15, 0, 1]] where
  M :=![![![377436988317, 86481650842, 42143298628], ![-5394342224384, 581568320699, 773944750406], ![-16463993532160, 445578575726, 1355513071105]]]
  hmulB := by decide  
  f := ![![![-443470260871558990057639, 98448857148009999216482, -42422812263808099040880]], ![![-180826906535948789241443, 40142944997229878292929, -17298084189779554574714]], ![![-92774413813766631364709, 20595597537006423947108, -8874893961031959492739]]]
  g := ![![![-44079684581, 86481650842, 42143298628], ![-399046985849, 581568320699, 773944750406], ![-465261245817, 445578575726, 1355513071105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-443470260871558990057639, 98448857148009999216482, -42422812263808099040880]] ![![377436988317, 86481650842, 42143298628]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-309677843083, 68747405239, -29624094688]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-309677843083, 68747405239, -29624094688]] 
 ![![151, 0, 0], ![0, 151, 0], ![108, 44, 1]] where
  M :=![![![-309677843083, 68747405239, -29624094688], ![3791884120064, -841785100368, 362735457921], ![-5007783750528, 1111710593885, -479049642447]]]
  hmulB := by decide  
  f := ![![![-468261, -71503, -25185]], ![![3223680, -530787, -601261]], ![![686396, -209015, -200712]]]
  g := ![![![19137247571, 9087467361, -29624094688], ![-234328114804, -111272485092, 362735457921], ![309467401548, 146952946103, -479049642447]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [24, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 150], [0, 1]]
 g := ![![[27, 64], [4, 34], [28, 2], [5], [46, 31], [124], [1]], ![[80, 87], [18, 117], [91, 149], [5], [41, 120], [124], [1]]]
 h' := ![![[107, 150], [55, 8], [83, 100], [126, 46], [104, 55], [16, 129], [127, 107], [0, 1]], ![[0, 1], [5, 143], [62, 51], [65, 105], [100, 96], [78, 22], [100, 44], [107, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [20, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [24, 44, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1304, -179, 219]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-148, -65, 219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-468261, -71503, -25185]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-468261, -71503, -25185]] 
 ![![151, 0, 0], ![141, 1, 0], ![3, 0, 1]] where
  M :=![![![-468261, -71503, -25185], ![3223680, -530787, -601261], ![12376064, -484313, -1132048]]]
  hmulB := by decide  
  f := ![![![-309677843083, 68747405239, -29624094688]], ![![-264057561289, 58619861181, -25260012537]], ![![-39316670727, 8728164302, -3761072361]]]
  g := ![![![64167, -71503, -25185], ![528930, -530787, -601261], ![556691, -484313, -1132048]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-309677843083, 68747405239, -29624094688]] ![![-468261, -71503, -25185]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3637210677, -171883810, -355072650]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![3637210677, -171883810, -355072650]] 
 ![![157, 0, 0], ![27, 1, 0], ![42, 0, 1]] where
  M :=![![![3637210677, -171883810, -355072650], ![45449299200, 247062957, -2623477270], ![67450426880, 2370149890, -2376414313]]]
  hmulB := by decide  
  f := ![![![-5630910415681096759, 1250042548596481030, -538658567474824750]], ![![-529212003736382449, 117483226168225323, -50624953831491720]], ![![-2086340044854637374, 463160241307715870, -199581392148790977]]]
  g := ![![![147714171, -171883810, -355072650], ![948819393, 247062957, -2623477270], ![657743828, 2370149890, -2376414313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8384440542569, 579814158350, -79453782924]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![8384440542569, 579814158350, -79453782924]] 
 ![![157, 0, 0], ![143, 1, 0], ![123, 0, 1]] where
  M :=![![![8384440542569, 579814158350, -79453782924], ![10170084214272, 5771006455355, 3740883976754], ![-64046128054528, 7331401136938, 9511890432109]]]
  hmulB := by decide  
  f := ![![![-27467260046003077004254443, 6097636299673736300506862, -2627545788623400342353920]], ![![-22875747297035953934949577, 5078336421869188543317281, -2188317049872125453646358]], ![![-24348054592820518943738045, 5405183526240518906854564, -2329159450174123433420815]]]
  g := ![![![-412459673897, 579814158350, -79453782924], ![-8122373044855, 5771006455355, 3740883976754], ![-14537573336217, 7331401136938, 9511890432109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![3637210677, -171883810, -355072650]] ![![8384440542569, 579814158350, -79453782924]]
  ![![51488932249894313532093, -1486216359560212145300, -4309399680510229751138]] where
 M := ![![![51488932249894313532093, -1486216359560212145300, -4309399680510229751138]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![51488932249894313532093, -1486216359560212145300, -4309399680510229751138]] ![![8384440542569, 579814158350, -79453782924]]
  ![![157, 0, 0]] where
 M := ![![![692591309288346473402376951250498181, -10316890005476501139710780713490394, -50641291000618940679089564954226174]]]
 hmul := by decide  
 g := ![![![![4411409613301569894282655740449033, -65712675194117841654208794353442, -322555993634515545726685127096982]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [139, 17, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [151, 52, 77], [95, 110, 86], [0, 1]]
 g := ![![[81, 128, 21], [72, 14, 96], [146, 118], [108, 16], [1, 143], [26, 83, 1], []], ![[86, 29, 38, 145], [84, 95, 47, 15], [99, 4], [89, 24], [13, 47], [43, 21, 154, 155], [31, 61]], ![[17, 13, 33, 20], [26, 130, 81, 45], [128, 60], [35, 85], [133, 133], [22, 103, 113, 106], [22, 61]]]
 h' := ![![[151, 52, 77], [98, 116, 64], [29, 121, 52], [33, 162, 97], [156, 71, 159], [135, 83, 119], [0, 0, 1], [0, 1]], ![[95, 110, 86], [118, 146, 161], [91, 63, 41], [117, 99, 161], [153, 46, 137], [2, 70, 84], [73, 15, 110], [151, 52, 77]], ![[0, 1], [13, 64, 101], [46, 142, 70], [87, 65, 68], [148, 46, 30], [78, 10, 123], [99, 148, 52], [95, 110, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 85], []]
 b := ![[], [55, 160, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [139, 17, 80, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8191891, 1504653, -276122]
  a := ![1, 7, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50257, 9231, -1694]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [146, 121, 140, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [151, 128, 158], [43, 38, 9], [0, 1]]
 g := ![![[39, 151, 63], [102, 57, 130], [68, 15, 36], [28, 54], [98, 28], [107, 27, 1], []], ![[126, 139, 80, 78], [65, 100, 137, 17], [56, 74, 135, 70], [161, 128], [134, 64], [63, 41, 122, 30], [50, 81]], ![[130, 55, 132, 127], [82, 83, 21, 28], [14, 46, 15, 24], [136, 122], [134, 126], [61, 136, 158, 162], [32, 81]]]
 h' := ![![[151, 128, 158], [138, 158, 49], [92, 86, 111], [145, 129, 6], [152, 82, 87], [76, 145, 144], [0, 0, 1], [0, 1]], ![[43, 38, 9], [148, 38, 106], [62, 129, 104], [72, 77, 69], [71, 60, 63], [116, 37, 159], [137, 72, 38], [151, 128, 158]], ![[0, 1], [34, 138, 12], [55, 119, 119], [110, 128, 92], [60, 25, 17], [98, 152, 31], [16, 95, 128], [43, 38, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 128], []]
 b := ![[], [99, 51, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [146, 121, 140, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3564782, 376251, 38911]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21346, 2253, 233]
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



lemma PB169I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 168 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 168 (by omega)

def PB169I3 : PrimesBelowBoundCertificateInterval O 137 168 169 where
  m := 6
  g := ![2, 2, 2, 3, 1, 1]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB169I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![4657463]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
  β := ![I139N1, I149N1, I151N1, I157N0, I157N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N0, I157N1, I157N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
