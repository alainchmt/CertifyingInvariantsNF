
import IdealArithmetic.Examples.NF3_1_432012_1.RI3_1_432012_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40, 21, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![40, 21, 0]] 
 ![![139, 0, 0], ![35, 1, 0], ![26, 0, 1]] where
  M :=![![![40, 21, 0], ![0, 40, 21], ![-1701, -777, 61]]]
  hmulB := by decide  
  f := ![![![18757, -1281, 441]], ![![4466, -305, 105]], ![![3998, -273, 94]]]
  g := ![![![-5, 21, 0], ![-14, 40, 21], ![172, -777, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![152383737090121529, 70108577190715029, -5200960827616677]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![152383737090121529, 70108577190715029, -5200960827616677]] 
 ![![139, 0, 0], ![121, 1, 0], ![93, 0, 1]] where
  M :=![![![152383737090121529, 70108577190715029, -5200960827616677], ![421277827036950837, 344819287711938578, 64907616363098352], ![-5257516925410966512, -1980303978397688187, 409726904075036930]]]
  hmulB := by decide  
  f := ![![![-269818550131726569301569480551253364, 18425886863037580373065494473926371, -6343972240054075835070699883997514]], ![![-231181171327298811099634391770488190, 15787343404156988933359505370516155, -5435530405924889723061581952329283]], ![![-187566620479944135342615396065113671, 12808909270909967262086404869435852, -4410065330588282816744848053706369]]]
  g := ![![![-56453703208762921, 70108577190715029, -5200960827616677], ![-340563052574645783, 344819287711938578, 64907616363098352], ![1411904045911732875, -1980303978397688187, 409726904075036930]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![40, 21, 0]] ![![152383737090121529, 70108577190715029, -5200960827616677]]
  ![![14942183851380828737, 10045548129579311298, 1155021510520398312]] where
 M := ![![![14942183851380828737, 10045548129579311298, 1155021510520398312]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![14942183851380828737, 10045548129579311298, 1155021510520398312]] ![![152383737090121529, 70108577190715029, -5200960827616677]]
  ![![139, 0, 0]] where
 M := ![![![436367362210619003131358673276907555, 2224180308241471358838919074121302273, 1047562258907291466287124532486396107]]]
 hmul := by decide  
 g := ![![![![3139333541083589950585314196236745, 16001297181593319128337547295836707, 7536419128829435009259888722923713]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44177242969446597890, -3016860332540311680, 1038695089360867019]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![44177242969446597890, -3016860332540311680, 1038695089360867019]] 
 ![![149, 0, 0], ![12, 1, 0], ![5, 0, 1]] where
  M :=![![![44177242969446597890, -3016860332540311680, 1038695089360867019], ![-84134302238230228539, 5745524663094518187, -1978165243179444661], ![160231384697535017541, -10942188240590776082, 3767359419915073526]]]
  hmulB := by decide  
  f := ![![![1887819160, 4548744122, 1867965927]], ![![-863432283, -84845575, 193505377]], ![![-3424928981, -2456240210, -345438795]]]
  g := ![![![504604641027691295, -3016860332540311680, 1038695089360867019], ![-961005181070249822, 5745524663094518187, -1978165243179444661], ![1830207023389590355, -10942188240590776082, 3767359419915073526]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10204304565655, 6575728609980, 639364731016]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![10204304565655, 6575728609980, 639364731016]] 
 ![![149, 0, 0], ![28, 1, 0], ![110, 0, 1]] where
  M :=![![![10204304565655, 6575728609980, 639364731016], ![-51788543212296, -13452190481937, 7215093340996], ![-584422560620676, -318746996829148, -6237097140941]]]
  hmulB := by decide  
  f := ![![![-2383691953078741857119834125, 162782129776915821849263188, -56045351855123226640398072]], ![![-417474504603622755983108132, 28509299995399064029223247, -9815658214910454702834100]], ![![-1817797274163267144262414954, 124137228138385206299081780, -42740039332758018836644485]]]
  g := ![![![-1639236355205, 6575728609980, 639364731016], ![-3146224679380, -13452190481937, 7215093340996], ![60581033799322, -318746996829148, -6237097140941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44397212, 3031882, -1043867]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-44397212, 3031882, -1043867]] 
 ![![149, 0, 0], ![108, 1, 0], ![107, 0, 1]] where
  M :=![![![-44397212, 3031882, -1043867], ![84553227, -5774133, 1988015], ![-161029215, 10996672, -3786118]]]
  hmulB := by decide  
  f := ![![![386, -3452, -1919]], ![![1323, -2023, -1427]], ![![3197, -102, -935]]]
  g := ![![![-1745951, 3031882, -1043867], ![3325114, -5774133, 1988015], ![-6332585, 10996672, -3786118]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![44177242969446597890, -3016860332540311680, 1038695089360867019]] ![![10204304565655, 6575728609980, 639364731016]]
  ![![386, -3452, -1919]] where
 M := ![![![386, -3452, -1919]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![386, -3452, -1919]] ![![-44397212, 3031882, -1043867]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9769716275018935, -3730745742987967, 734659067770877]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-9769716275018935, -3730745742987967, 734659067770877]] 
 ![![151, 0, 0], ![0, 151, 0], ![33, 24, 1]] where
  M :=![![![-9769716275018935, -3730745742987967, 734659067770877], ![-59507384489441037, -36952101782541384, -2996086675217090], ![242683020692584290, 51347822493591293, -39948188457758474]]]
  hmulB := by decide  
  f := ![![![-10794781805918525122645498612486, 737174772342100778085219656347, -253806849383612884977045465098]], ![![20558354800072643683140682672938, -1403928378724848378494816403860, 483367922958487893108174191249]], ![![649138502296652980174257089055, -44329615572837375953146406864, 15262540831643203609053231981]]]
  g := ![![![-225254738486476, -141473929599265, 734659067770877], ![260685270150483, 231483300812376, -2996086675217090], ![10337571124494132, 6689432751521819, -39948188457758474]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [28, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 150], [0, 1]]
 g := ![![[136, 110], [112, 11], [4, 19], [78], [140, 10], [32], [1]], ![[130, 41], [51, 140], [132, 132], [78], [112, 141], [32], [1]]]
 h' := ![![[118, 150], [35, 84], [39, 39], [117, 64], [6, 94], [39, 37], [123, 118], [0, 1]], ![[0, 1], [132, 67], [111, 112], [119, 87], [75, 57], [26, 114], [4, 33], [118, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [108, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [28, 33, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-215, -225, -66]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 9, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10794781805918525122645498612486, 737174772342100778085219656347, -253806849383612884977045465098]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-10794781805918525122645498612486, 737174772342100778085219656347, -253806849383612884977045465098]] 
 ![![151, 0, 0], ![126, 1, 0], ![130, 0, 1]] where
  M :=![![![-10794781805918525122645498612486, 737174772342100778085219656347, -253806849383612884977045465098], ![20558354800072643683140682672938, -1403928378724848378494816403860, 483367922958487893108174191249], ![-39152801759637519341762109491169, 2673741650608591638138237596725, -920560455766360485386642212611]]]
  hmulB := by decide  
  f := ![![![-9769716275018935, -3730745742987967, 734659067770877]], ![![-8546302219482297, -3357788512576326, 593185138171612]], ![![-6803841689138260, -2871848503939367, 367930399685136]]]
  g := ![![![-468105382126844689499120959268, 737174772342100778085219656347, -253806849383612884977045465098], ![891493381025166313042549037728, -1403928378724848378494816403860, 483367922958487893108174191249], ![-1697823778057570878456401053239, 2673741650608591638138237596725, -920560455766360485386642212611]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-9769716275018935, -3730745742987967, 734659067770877]] ![![-10794781805918525122645498612486, 737174772342100778085219656347, -253806849383612884977045465098]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [87, 132, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 155, 85], [22, 1, 72], [0, 1]]
 g := ![![[149, 36, 19], [136, 12], [103, 13, 130], [19, 147, 75], [1, 47, 108], [90, 1], []], ![[25, 88, 86, 54], [46, 117], [117, 47, 99, 112], [152, 137, 29, 129], [132, 102, 105, 45], [77, 1], [87, 3]], ![[12, 64, 15, 123], [64, 140], [144, 93, 39, 72], [51, 121, 112, 84], [130, 82, 70, 21], [20, 4], [100, 3]]]
 h' := ![![[68, 155, 85], [87, 27, 126], [145, 12, 13], [74, 122, 75], [70, 104, 46], [20, 122, 118], [0, 0, 1], [0, 1]], ![[22, 1, 72], [117, 69, 66], [42, 127, 91], [73, 132, 83], [98, 121, 94], [83, 88, 126], [38, 72, 1], [68, 155, 85]], ![[0, 1], [95, 61, 122], [47, 18, 53], [114, 60, 156], [123, 89, 17], [22, 104, 70], [105, 85, 155], [22, 1, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 32], []]
 b := ![[], [42, 77, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [87, 132, 67, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![192639, 121518, 15386]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1227, 774, 98]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15643776316801754705749, -1068312213460975067637, 367816381175254769101]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![15643776316801754705749, -1068312213460975067637, 367816381175254769101]] 
 ![![163, 0, 0], ![0, 163, 0], ![156, 127, 1]] where
  M :=![![![15643776316801754705749, -1068312213460975067637, 367816381175254769101], ![-29793126875195636297181, 2034570213317328249012, -700495832285720298536], ![56740162415143344181416, -3874781080623985251349, 1334074381031607950476]]]
  hmulB := by decide  
  f := ![![![-37363096904, -18757039399, 452396940]], ![![-36644152140, -54101783684, -18304642459]], ![![-55213339875, -56174215063, -14273141692]]]
  g := ![![![-256046497831521406589, -293134924065756630328, 367816381175254769101], ![487633269701697731745, 558267122169348504068, -700495832285720298536], ![-928683687274769914680, -1063203849519252729827, 1334074381031607950476]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [25, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 162], [0, 1]]
 g := ![![[30, 150], [157, 133], [119], [97], [87], [143, 150], [1]], ![[0, 13], [0, 30], [119], [97], [87], [113, 13], [1]]]
 h' := ![![[65, 162], [150, 98], [8, 40], [7, 114], [65, 74], [11, 139], [138, 65], [0, 1]], ![[0, 1], [0, 65], [0, 123], [82, 49], [148, 89], [81, 24], [125, 98], [65, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [148, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [25, 98, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2070, -74, -7]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 5, -7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37363096904, 18757039399, -452396940]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![37363096904, 18757039399, -452396940]] 
 ![![163, 0, 0], ![35, 1, 0], ![79, 0, 1]] where
  M :=![![![37363096904, 18757039399, -452396940], ![36644152140, 54101783684, 18304642459], ![-1482676039179, -640627618843, 72406426143]]]
  hmulB := by decide  
  f := ![![![-15643776316801754705749, 1068312213460975067637, -367816381175254769101]], ![![-3176313154680158149718, 216910167225869933241, -74681457109498138773]], ![![-7930052094739153165249, 541542613153625862544, -186451340453231501285]]]
  g := ![![![-3579103827, 18757039399, -452396940], ![-20263711847, 54101783684, 18304642459], ![93369220583, -640627618843, 72406426143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![15643776316801754705749, -1068312213460975067637, 367816381175254769101]] ![![37363096904, 18757039399, -452396940]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![274550254429, -18749014565, 6455224045]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![274550254429, -18749014565, 6455224045]] 
 ![![167, 0, 0], ![0, 167, 0], ![94, 39, 1]] where
  M :=![![![274550254429, -18749014565, 6455224045], ![-522873147645, 35706964764, -12293790520], ![995797032120, -68002898405, 23413174244]]]
  hmulB := by decide  
  f := ![![![-70552, -55595, -9740]], ![![788940, 289828, -65335]], ![![176221, 55591, -19396]]]
  g := ![![![-1989465903, -1619776960, 6455224045], ![3788881205, 3084819132, -12293790520], ![-7215816448, -5874950263, 23413174244]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [73, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 166], [0, 1]]
 g := ![![[53, 132], [28, 114], [113, 38], [62], [47], [5, 116], [1]], ![[31, 35], [9, 53], [51, 129], [62], [47], [97, 51], [1]]]
 h' := ![![[139, 166], [127, 93], [101, 92], [39, 120], [35, 79], [136, 61], [94, 139], [0, 1]], ![[0, 1], [28, 74], [30, 75], [19, 47], [161, 88], [98, 106], [43, 28], [139, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [133, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [73, 28, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141, -810, -419]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![235, 93, -419]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70552, -55595, -9740]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-70552, -55595, -9740]] 
 ![![167, 0, 0], ![127, 1, 0], ![70, 0, 1]] where
  M :=![![![-70552, -55595, -9740], ![788940, 289828, -65335], ![5292135, 3206335, 224493]]]
  hmulB := by decide  
  f := ![![![274550254429, -18749014565, 6455224045]], ![![205658737514, -14044418473, 4835447085]], ![![121043801450, -8266071365, 2845981182]]]
  g := ![![![45939, -55595, -9740], ![-188298, 289828, -65335], ![-2500760, 3206335, 224493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![274550254429, -18749014565, 6455224045]] ![![-70552, -55595, -9740]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [115, 118, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 22, 148], [113, 150, 25], [0, 1]]
 g := ![![[50, 131, 119], [133, 148], [99, 41, 60], [112, 161, 23], [50, 31], [49, 72, 1], []], ![[120, 0, 98, 113], [82, 130], [8, 104, 16, 142], [42, 46, 126, 144], [90, 106], [20, 110, 6, 96], [131, 106]], ![[127, 153, 75, 172], [49, 159], [71, 14, 167, 142], [65, 21, 58, 106], [147, 150], [102, 27, 94, 163], [81, 106]]]
 h' := ![![[132, 22, 148], [153, 80, 130], [33, 67, 119], [95, 95, 135], [72, 64, 14], [74, 124, 107], [0, 0, 1], [0, 1]], ![[113, 150, 25], [101, 106, 27], [169, 109, 86], [151, 53, 56], [26, 128, 154], [13, 137, 148], [110, 131, 150], [132, 22, 148]], ![[0, 1], [109, 160, 16], [143, 170, 141], [159, 25, 155], [127, 154, 5], [123, 85, 91], [167, 42, 22], [113, 150, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 66], []]
 b := ![[], [37, 64, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [115, 118, 101, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45326, -31486, -3979]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-262, -182, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101881576003366, 6957484546372, -2395439044583]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-101881576003366, 6957484546372, -2395439044583]] 
 ![![179, 0, 0], ![0, 179, 0], ![133, 28, 1]] where
  M :=![![![-101881576003366, 6957484546372, -2395439044583], ![194030562611223, -13250331353795, 4562045501789], ![-369525685644909, 25234879045030, -8688285852006]]]
  hmulB := by decide  
  f := ![![![2682100, 1108102, -157637]], ![![12768597, 8514669, 950465]], ![![3560069, 2030110, 84427]]]
  g := ![![![1210680541487, 413574177624, -2395439044583], ![-2305706643166, -787640253653, 4562045501789], ![4391152696491, 1500038451962, -8688285852006]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [124, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [167, 178], [0, 1]]
 g := ![![[156, 13], [95, 172], [16], [151], [167, 57], [174, 144], [1]], ![[0, 166], [0, 7], [16], [151], [20, 122], [57, 35], [1]]]
 h' := ![![[167, 178], [34, 152], [31, 107], [164, 175], [56, 144], [83, 86], [55, 167], [0, 1]], ![[0, 1], [0, 27], [0, 72], [33, 4], [118, 35], [125, 93], [20, 12], [167, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [177, 119]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [124, 12, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3022, -1258, 377]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-297, -66, 377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2682100, -1108102, 157637]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-2682100, -1108102, 157637]] 
 ![![179, 0, 0], ![150, 1, 0], ![54, 0, 1]] where
  M :=![![![-2682100, -1108102, 157637], ![-12768597, -8514669, -950465], ![76987665, 22398608, -9465134]]]
  hmulB := by decide  
  f := ![![![101881576003366, -6957484546372, 2395439044583]], ![![84291652725663, -5756270115095, 1981864866959]], ![![32799613350987, -2239882930442, 771184325472]]]
  g := ![![![866038, -1108102, 157637], ![7350597, -8514669, -950465], ![-15484281, 22398608, -9465134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-101881576003366, 6957484546372, -2395439044583]] ![![-2682100, -1108102, 157637]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14216523996146, 14004184973177, 3433693701226]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![14216523996146, 14004184973177, 3433693701226]] 
 ![![181, 0, 0], ![0, 181, 0], ![130, 139, 1]] where
  M :=![![![14216523996146, 14004184973177, 3433693701226], ![-278129189799306, -112830142949216, 17437878674403], ![-1412468172626643, -923330700752217, -95392264274813]]]
  hmulB := by decide  
  f := ![![![-148420174311851956874311039, 10135601643131551520958161, -3489654307454753100919487]], ![![282661998903835001174478447, -19302964936026092140290020, 6645947335676798420038674]], ![![107497643386201602748999649, -7341005331584152763219361, 2527483989445346870417630]]]
  g := ![![![-2387644514714, -2559553809377, 3433693701226], ![-14061068604816, -14014891042493, 17437878674403], ![60710089409387, 68155768140590, -95392264274813]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [173, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 180], [0, 1]]
 g := ![![[99, 55], [1], [48, 94], [154], [61, 145], [37, 99], [1]], ![[38, 126], [1], [105, 87], [154], [147, 36], [72, 82], [1]]]
 h' := ![![[68, 180], [130, 112], [22, 1], [94, 128], [126, 71], [115, 114], [8, 68], [0, 1]], ![[0, 1], [144, 69], [90, 180], [110, 53], [67, 110], [84, 67], [107, 113], [68, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [100, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [173, 113, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![466, 437, -144]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![106, 113, -144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![148420174311851956874311039, -10135601643131551520958161, 3489654307454753100919487]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![148420174311851956874311039, -10135601643131551520958161, 3489654307454753100919487]] 
 ![![181, 0, 0], ![41, 1, 0], ![129, 0, 1]] where
  M :=![![![148420174311851956874311039, -10135601643131551520958161, 3489654307454753100919487], ![-282661998903835001174478447, 19302964936026092140290020, -6645947335676798420038674], ![538321734189820672023132594, -36761947483793459633047509, 12657017600349293720251346]]]
  hmulB := by decide  
  f := ![![![-14216523996146, -14004184973177, -3433693701226]], ![![-1683692232280, -2548847740061, -874139891849]], ![![-2328527198211, -4879608623136, -1920189078361]]]
  g := ![![![628809038776698448701557, -10135601643131551520958161, 3489654307454753100919487], ![-1197548922533689407410941, 19302964936026092140290020, -6645947335676798420038674], ![2280697848509909541799209, -36761947483793459633047509, 12657017600349293720251346]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![14216523996146, 14004184973177, 3433693701226]] ![![148420174311851956874311039, -10135601643131551520958161, 3489654307454753100919487]]
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


lemma PB186I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 185 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 185 (by omega)

def PB186I3 : PrimesBelowBoundCertificateInterval O 137 185 186 where
  m := 9
  g := ![3, 3, 2, 1, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB186I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
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
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![32761, 181]
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
      exact NI149N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
  β := ![I139N0, I139N1, I149N0, I149N1, I149N2, I151N1, I163N1, I167N1, I179N1, I181N1]
  Il := ![[I139N0, I139N1, I139N1], [I149N0, I149N1, I149N2], [I151N1], [], [I163N1], [I167N1], [], [I179N1], [I181N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
