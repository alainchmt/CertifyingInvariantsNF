
import IdealArithmetic.Examples.NF3_1_679112_1.RI3_1_679112_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30283091, 11930108, 1174502]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![30283091, 11930108, 1174502]] 
 ![![197, 0, 0], ![41, 1, 0], ![92, 0, 1]] where
  M :=![![![30283091, 11930108, 1174502], ![-185571316, 27934087, 13104610], ![-2070528380, -211780536, 41038697]]]
  hmulB := by decide  
  f := ![![![3921679862235599, -738332750482348, 123530771548206]], ![![717111738309863, -135010276399173, 22588627688032]], ![![2324534314706952, -437638939041240, 73221560013401]]]
  g := ![![![-2877693, 11930108, 1174502], ![-12875599, 27934087, 13104610], ![14400576, -211780536, 41038697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11226587160558141008494972448723723893752725, -2113624076407779440165171538700100281247714, 353631357610703205285247825079241323930410]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![11226587160558141008494972448723723893752725, -2113624076407779440165171538700100281247714, 353631357610703205285247825079241323930410]] 
 ![![197, 0, 0], ![59, 1, 0], ![65, 0, 1]] where
  M :=![![![11226587160558141008494972448723723893752725, -2113624076407779440165171538700100281247714, 353631357610703205285247825079241323930410], ![-55873754502491106435069156362520129181004780, 10519324445336734597924476798565241245891905, -1759992718797076234879923713620858957317304], ![278078849569938045111027946752095715256134032, -52353769064896953965309308935278411266370172, 8759331726539658363044553084944382288574601]]]
  hmulB := by decide  
  f := ![![![-28159077142585550551383, -9040812499566178018406, -679712982465279687994]], ![![-7888278681132148689485, -2843693343411469514017, -252911631713111468518]], ![![-1494908569071525219435, -2339173148620428756754, -409652388426038723865]]]
  g := ![![![573321672202646800176136977674512459045133, -2113624076407779440165171538700100281247714, 353631357610703205285247825079241323930410], ![-2853372436830195393123950487779256499812195, 10519324445336734597924476798565241245891905, -1759992718797076234879923713620858957317304], ![14200988132861830129270970677218970209211295, -52353769064896953965309308935278411266370172, 8759331726539658363044553084944382288574601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-471775188687829, -42493543006326, 10508355779792]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-471775188687829, -42493543006326, 10508355779792]] 
 ![![197, 0, 0], ![96, 1, 0], ![43, 0, 1]] where
  M :=![![![-471775188687829, -42493543006326, 10508355779792], ![-1660320213207136, -492791900247413, -31985187226534], ![5053659581792372, -1596349838754068, -524777087473947]]]
  hmulB := by decide  
  f := ![![![207546349670992989809461608799, -39074649789950005779433382578, 6537596542175696677702732180]], ![![95895986369297294145336460712, -18054290473342938874982480117, 3020671141122297319582394106]], ![![71397702786807306598377116453, -13442010599675440128879217434, 2248988602296559616718492273]]]
  g := ![![![16019013408063, -42493543006326, 10508355779792], ![238695762747642, -492791900247413, -31985187226534], ![918115019611993, -1596349838754068, -524777087473947]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![30283091, 11930108, 1174502]] ![![11226587160558141008494972448723723893752725, -2113624076407779440165171538700100281247714, 353631357610703205285247825079241323930410]]
  ![![207546349670992989809461608799, -39074649789950005779433382578, 6537596542175696677702732180]] where
 M := ![![![207546349670992989809461608799, -39074649789950005779433382578, 6537596542175696677702732180]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![207546349670992989809461608799, -39074649789950005779433382578, 6537596542175696677702732180]] ![![-471775188687829, -42493543006326, 10508355779792]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-926176523, -906456366, -144740670]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-926176523, -906456366, -144740670]] 
 ![![199, 0, 0], ![0, 199, 0], ![127, 62, 1]] where
  M :=![![![-926176523, -906456366, -144740670], ![22869025860, -636695183, -1051197036], ![166089131688, 24971419932, -1687892219]]]
  hmulB := by decide  
  f := ![![![137309323932111571, -25851159290670606, 4325168632308234]], ![![-683376643904700972, 128658986667495103, -21525990658362372]], ![![-108190760093929829, 20369021511967604, -3407949791488385]]]
  g := ![![![87718033, 40540026, -144740670], ![785784168, 324309151, -1051197036], ![1911816299, 651360490, -1687892219]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [24, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 198], [0, 1]]
 g := ![![[147, 106], [152, 106], [], [128], [18], [92], [54, 1]], ![[100, 93], [105, 93], [], [128], [18], [92], [108, 198]]]
 h' := ![![[54, 198], [133, 92], [0, 92], [93], [141, 39], [37, 60], [97, 106], [0, 1]], ![[0, 1], [126, 107], [192, 107], [93], [58, 160], [93, 139], [50, 93], [54, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [25, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [24, 145, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-450, -309, -143]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![89, 43, -143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137309323932111571, -25851159290670606, 4325168632308234]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![137309323932111571, -25851159290670606, 4325168632308234]] 
 ![![199, 0, 0], ![136, 1, 0], ![11, 0, 1]] where
  M :=![![![137309323932111571, -25851159290670606, 4325168632308234], ![-683376643904700972, 128658986667495103, -21525990658362372], ![3401106524021254776, -640324662587976228, 107132996009132731]]]
  hmulB := by decide  
  f := ![![![-926176523, -906456366, -144740670]], ![![-518045132, -622687241, -104200644]], ![![783423065, 75378894, -16482611]]]
  g := ![![![18118040866873987, -25851159290670606, 4325168632308234], ![-90171924288653512, 128658986667495103, -21525990658362372], ![448777877788369657, -640324662587976228, 107132996009132731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-926176523, -906456366, -144740670]] ![![137309323932111571, -25851159290670606, 4325168632308234]]
  ![![199, 0, 0]] where
 M := ![![![199, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23094982279896396903, -4348081023456215869, 727479315025320689]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![23094982279896396903, -4348081023456215869, 727479315025320689]] 
 ![![211, 0, 0], ![0, 211, 0], ![71, 184, 1]] where
  M :=![![![23094982279896396903, -4348081023456215869, 727479315025320689], ![-114941731774000668862, 21640023649845755525, -3620601708430895180], ![572055069932081438440, -107700528357138878502, 18019421941414860345]]]
  hmulB := by decide  
  f := ![![![2870946615, -310664043, -178326755]], ![![28175627290, 3227600125, -488990798]], ![![25902432119, 2848222203, -473445010]]]
  g := ![![![-135336725530338256, -654996563924716695, 727479315025320689], ![673559192059681938, 3259861317540902695, -3620601708430895180], ![-3352245914257695005, -16224048178092289962, 18019421941414860345]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [162, 194, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 210], [0, 1]]
 g := ![![[108, 1], [16, 45], [173], [58], [85, 66], [93], [17, 1]], ![[125, 210], [148, 166], [173], [58], [152, 145], [93], [34, 210]]]
 h' := ![![[17, 210], [151, 1], [30, 195], [170, 157], [156, 67], [36, 53], [200, 127], [0, 1]], ![[0, 1], [168, 210], [180, 16], [96, 54], [29, 144], [93, 158], [38, 84], [17, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154]]
 b := ![[], [84, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [162, 194, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![443, -1800, 559]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-186, -496, 559]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2870946615, -310664043, -178326755]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![2870946615, -310664043, -178326755]] 
 ![![211, 0, 0], ![26, 1, 0], ![168, 0, 1]] where
  M :=![![![2870946615, -310664043, -178326755], ![28175627290, 3227600125, -488990798], ![77260546084, 29153608886, 2738609327]]]
  hmulB := by decide  
  f := ![![![23094982279896396903, -4348081023456215869, 727479315025320689]], ![![2301079656413770856, -433223141990596479, 72482751100603994]], ![![21099583378932114304, -3972408247856792154, 664625340595586427]]]
  g := ![![![193872543, -310664043, -178326755], ![125158664, 3227600125, -488990798], ![-5406728208, 29153608886, 2738609327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![23094982279896396903, -4348081023456215869, 727479315025320689]] ![![2870946615, -310664043, -178326755]]
  ![![211, 0, 0]] where
 M := ![![![211, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [51, 26, 188, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 161, 163], [147, 61, 60], [0, 1]]
 g := ![![[129, 185, 153], [83, 61, 69], [40, 24, 169], [93, 157, 30], [100, 128, 65], [23, 110], [1]], ![[136, 206, 220, 61], [195, 194, 194, 155], [22, 197, 177, 145], [147, 182, 8, 44], [85, 136, 171, 206], [126, 73], [99, 135, 215, 87]], ![[197, 11, 87, 4], [28, 157, 195, 133], [54, 43, 134, 136], [204, 212, 22, 172], [172, 217, 74, 64], [124, 153], [180, 25, 135, 136]]]
 h' := ![![[111, 161, 163], [4, 57, 162], [190, 221, 31], [163, 5, 13], [29, 87, 132], [90, 12, 180], [172, 197, 35], [0, 1]], ![[147, 61, 60], [185, 57, 218], [207, 105, 4], [178, 164, 47], [86, 208, 156], [69, 124, 2], [52, 195, 127], [111, 161, 163]], ![[0, 1], [64, 109, 66], [117, 120, 188], [185, 54, 163], [192, 151, 158], [44, 87, 41], [74, 54, 61], [147, 61, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 74], []]
 b := ![[], [197, 134, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [51, 26, 188, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![481011, -11596, 11596]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2157, -52, 52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-365898936086938573016969901408979116261, 68887613821090723899514930937421991874, -11525616437676424849343005468293663822]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-365898936086938573016969901408979116261, 68887613821090723899514930937421991874, -11525616437676424849343005468293663822]] 
 ![![227, 0, 0], ![0, 227, 0], ![140, 53, 1]] where
  M :=![![![-365898936086938573016969901408979116261, 68887613821090723899514930937421991874, -11525616437676424849343005468293663822], ![1821047397152875126196194863990398883876, -342847703211585723318283890472391788617, 57361997383414299050171925469128328052], ![-9063195586579459249927164224122275832216, 1706323402386046528095851013052142227772, -285485705828171424268111965003263460565]]]
  hmulB := by decide  
  f := ![![![-16071886858134248143, -3489806757944622838, -52345467587955662]], ![![8270583878896994596, -15967195922958336819, -3542152225532578500]], ![![-5515696752965227416, -5812684765194171353, -945250139048596337]]]
  g := ![![![5496420110959299144894497198908078497, 2994472621224410752928168373378793720, -11525616437676424849343005468293663822], ![-27355208090419060532281386351046550852, -14903231561817372568182360970644022799, 57361997383414299050171925469128328052], ![136144507618345991839685069939800038092, 74172096084930096979320639463546720871, -285485705828171424268111965003263460565]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [27, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 226], [0, 1]]
 g := ![![[182, 185], [23, 82], [27], [73], [4], [74, 62], [80, 1]], ![[0, 42], [0, 145], [27], [73], [4], [40, 165], [160, 226]]]
 h' := ![![[80, 226], [60, 56], [138, 38], [58, 150], [101, 46], [45, 2], [110, 17], [0, 1]], ![[0, 1], [0, 171], [0, 189], [27, 77], [149, 181], [205, 225], [108, 210], [80, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [169, 149]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [27, 147, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-299, -1279, -461]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![283, 102, -461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16071886858134248143, 3489806757944622838, 52345467587955662]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![16071886858134248143, 3489806757944622838, 52345467587955662]] 
 ![![227, 0, 0], ![173, 1, 0], ![35, 0, 1]] where
  M :=![![![16071886858134248143, 3489806757944622838, 52345467587955662], ![-8270583878896994596, 15967195922958336819, 3542152225532578500], ![-559660051634147403000, -15354888329962151596, 19509348148490915319]]]
  hmulB := by decide  
  f := ![![![365898936086938573016969901408979116261, -68887613821090723899514930937421991874, 11525616437676424849343005468293663822]], ![![270834663197742281963610564228030785151, -50989909638048940578404401593399175355, 8531143816452014096414837094914870102]], ![![96342107267058631301855113539368039213, -18138281436670580901228518043444546006, 3034723705492714951520339896006791605]]]
  g := ![![![-2596902086483982163, 3489806757944622838, 52345467587955662], ![-12751413244248147629, 15967195922958336819, 3542152225532578500], ![6228671560582038709, -15354888329962151596, 19509348148490915319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-365898936086938573016969901408979116261, 68887613821090723899514930937421991874, -11525616437676424849343005468293663822]] ![![16071886858134248143, 3489806757944622838, 52345467587955662]]
  ![![227, 0, 0]] where
 M := ![![![-227, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7525300955237111, -8937569486120770, -2099616750079460]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![7525300955237111, -8937569486120770, -2099616750079460]] 
 ![![229, 0, 0], ![0, 229, 0], ![103, 182, 1]] where
  M :=![![![7525300955237111, -8937569486120770, -2099616750079460], ![331739446512554680, 11724534455396031, -11037186236200230], ![1743875425319636340, 353813818984955140, 687348219195801]]]
  hmulB := by decide  
  f := ![![![17088069218152850548817599977939, -3217162437904672552304711670470, 538264837758640136658832752840]], ![![-85045844365865141592095574948720, 16011539542635570275499934472259, -2678897600146032415645878917630]], ![![-58056797922684013281926344864427, 10930324962838076159357200675892, -1828757392991041169047319362059]]]
  g := ![![![977230682154679, 1629662353835550, -2099616750079460], ![6412967811533530, 8823111045606279, -11037186236200230], ![7306019907172353, 998761760224102, 687348219195801]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [210, 218, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 228], [0, 1]]
 g := ![![[97, 12], [37], [6, 20], [75], [103], [7, 135], [11, 1]], ![[0, 217], [37], [226, 209], [75], [103], [118, 94], [22, 228]]]
 h' := ![![[11, 228], [188, 87], [114, 91], [65, 97], [181, 103], [133, 65], [209, 140], [0, 1]], ![[0, 1], [0, 142], [199, 138], [216, 132], [169, 126], [161, 164], [146, 89], [11, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [107, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [210, 218, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-264, -382, -216]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![96, 170, -216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17088069218152850548817599977939, -3217162437904672552304711670470, 538264837758640136658832752840]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![17088069218152850548817599977939, -3217162437904672552304711670470, 538264837758640136658832752840]] 
 ![![229, 0, 0], ![46, 1, 0], ![174, 0, 1]] where
  M :=![![![17088069218152850548817599977939, -3217162437904672552304711670470, 538264837758640136658832752840], ![-85045844365865141592095574948720, 16011539542635570275499934472259, -2678897600146032415645878917630], ![423265820823073121672048868985540, -79688049165573076760803817113460, 13332641942489537859854055554629]]]
  hmulB := by decide  
  f := ![![![7525300955237111, -8937569486120770, -2099616750079460]], ![![2960276377526034, -1744120794350041, -469954396243910]], ![![13333090792711326, -5245953151091960, -1592340464168691]]]
  g := ![![![311875369396351109939726802731, -3217162437904672552304711670470, 538264837758640136658832752840], ![-1552176772496470453898295323166, 16011539542635570275499934472259, -2678897600146032415645878917630], ![7725049713739105087573881177726, -79688049165573076760803817113460, 13332641942489537859854055554629]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![7525300955237111, -8937569486120770, -2099616750079460]] ![![17088069218152850548817599977939, -3217162437904672552304711670470, 538264837758640136658832752840]]
  ![![229, 0, 0]] where
 M := ![![![229, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -36, -6]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-31, -36, -6]] 
 ![![233, 0, 0], ![0, 233, 0], ![44, 6, 1]] where
  M :=![![![-31, -36, -6], ![948, -19, -42], ![6636, 1032, -61]]]
  hmulB := by decide  
  f := ![![![-191, 36, -6]], ![![948, -179, 30]], ![![-32, 6, -1]]]
  g := ![![![1, 0, -6], ![12, 1, -42], ![40, 6, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [57, 164, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 232], [0, 1]]
 g := ![![[195, 183], [58], [1], [103, 14], [132], [209, 72], [69, 1]], ![[7, 50], [58], [1], [137, 219], [132], [51, 161], [138, 232]]]
 h' := ![![[69, 232], [2, 154], [195, 161], [187, 232], [133, 108], [203, 150], [28, 44], [0, 1]], ![[0, 1], [143, 79], [120, 72], [118, 1], [129, 125], [68, 83], [35, 189], [69, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189]]
 b := ![[], [60, 211]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [57, 164, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5940, 2918, 564]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-132, -2, 564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, -36, 6]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![191, -36, 6]] 
 ![![233, 0, 0], ![226, 1, 0], ![184, 0, 1]] where
  M :=![![![191, -36, 6], ![-948, 179, -30], ![4740, -888, 149]]]
  hmulB := by decide  
  f := ![![![31, 36, 6]], ![![26, 35, 6]], ![![-4, 24, 5]]]
  g := ![![![31, -36, 6], ![-154, 179, -30], ![764, -888, 149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-31, -36, -6]] ![![191, -36, 6]]
  ![![233, 0, 0]] where
 M := ![![![-233, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)


lemma PB234I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 233 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 233 (by omega)

def PB234I4 : PrimesBelowBoundCertificateInterval O 193 233 234 where
  m := 7
  g := ![3, 2, 2, 1, 2, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233]
  hP := PB234I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
  β := ![I197N0, I197N1, I197N2, I199N1, I211N1, I227N1, I229N1, I233N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [I211N1], [], [I227N1], [I229N1], [I233N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
