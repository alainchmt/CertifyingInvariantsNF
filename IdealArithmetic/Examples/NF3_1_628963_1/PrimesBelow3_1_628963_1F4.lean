
import IdealArithmetic.Examples.NF3_1_628963_1.RI3_1_628963_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117401660, -12931190, -6393821]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-117401660, -12931190, -6393821]] 
 ![![197, 0, 0], ![0, 197, 0], ![152, 187, 1]] where
  M :=![![![-117401660, -12931190, -6393821], ![-952392233, -104901114, -51868308], ![-1211213550, -133408953, -65963996]]]
  hmulB := by decide  
  f := ![![![-660, 791, -558]], ![![-86956, 4270, 5071]], ![![-82097, 4546, 4383]]]
  g := ![![![4337356, 6003621, -6393821], ![35185739, 48702906, -51868308], ![44747786, 61938367, -65963996]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [86, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [147, 196], [0, 1]]
 g := ![![[193, 54], [190], [23, 155], [96], [163], [136], [147, 1]], ![[54, 143], [190], [153, 42], [96], [163], [136], [97, 196]]]
 h' := ![![[147, 196], [75, 60], [189, 92], [114, 130], [117, 80], [98, 44], [163, 50], [0, 1]], ![[0, 1], [30, 137], [120, 105], [115, 67], [57, 117], [65, 153], [27, 147], [147, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [112, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [86, 50, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1762, 501, -385]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![306, 368, -385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-660, 791, -558]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-660, 791, -558]] 
 ![![197, 0, 0], ![52, 1, 0], ![29, 0, 1]] where
  M :=![![![-660, 791, -558], ![-86956, 4270, 5071], ![187983, -23160, -10]]]
  hmulB := by decide  
  f := ![![![-117401660, -12931190, -6393821]], ![![-35823749, -3945802, -1951000]], ![![-23430770, -2580779, -1276065]]]
  g := ![![![-130, 791, -558], ![-2315, 4270, 5071], ![7069, -23160, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-117401660, -12931190, -6393821]] ![![-660, 791, -558]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-429663236730267840275727460931813828, -47325199233162760539807962973973197, -23399923187028870566419090765918438]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-429663236730267840275727460931813828, -47325199233162760539807962973973197, -23399923187028870566419090765918438]] 
 ![![199, 0, 0], ![0, 199, 0], ![147, 70, 1]] where
  M :=![![![-429663236730267840275727460931813828, -47325199233162760539807962973973197, -23399923187028870566419090765918438], ![-3485537849149091675582504961237574620, -383914096074420137956828842284249594, -189826149791756061566201633338029109], ![-4432764700230437894620327443107686581, -488246269772976165452982217431469272, -241413145515826836930435171920193682]]]
  hmulB := by decide  
  f := ![![![224731223638518460, 21587748524932182, -38757676331322499]], ![![-5973099975742206711, 500452778676317818, 185454095287305908]], ![![-1895113878105622776, 184907355429266545, 38296455685029901]]]
  g := ![![![15126258652075256949687833576171842, 7993313687732955673917228093669937, -23399923187028870566419090765918438], ![122708071207231403892709221806294997, 64843800951500020963202439655164764, -189826149791756061566201633338029109], ![156055114023096015749515793111360727, 82465698072034685526017486517497932, -241413145515826836930435171920193682]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [55, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [133, 198], [0, 1]]
 g := ![![[41, 25], [36, 9], [179, 1], [65], [140], [158], [133, 1]], ![[182, 174], [39, 190], [113, 198], [65], [140], [158], [67, 198]]]
 h' := ![![[133, 198], [10, 194], [105, 3], [176, 198], [186, 57], [181, 90], [48, 122], [0, 1]], ![[0, 1], [141, 5], [106, 196], [43, 1], [6, 142], [12, 109], [155, 77], [133, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [145, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [55, 66, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10194, 4584, 20]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, 16, 20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-224731223638518460, -21587748524932182, 38757676331322499]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-224731223638518460, -21587748524932182, 38757676331322499]] 
 ![![199, 0, 0], ![50, 1, 0], ![196, 0, 1]] where
  M :=![![![-224731223638518460, -21587748524932182, 38757676331322499], ![5973099975742206711, -500452778676317818, -185454095287305908], ![-7953846684073323726, 1408529810083235559, -336586431913944092]]]
  hmulB := by decide  
  f := ![![![429663236730267840275727460931813828, 47325199233162760539807962973973197, 23399923187028870566419090765918438]], ![![125470852691771274820949135717729980, 13819970139359588768579030105441756, 6833277935392962763252041063487191]], ![![445461101001823791902828692390669331, 49065252861672749905805743519247316, 24260291910419524964565713377086470]]]
  g := ![![![-33878634966488036, -21587748524932182, 38757676331322499], ![338415786863668621, -500452778676317818, -185454095287305908], ![-62358776548251556, 1408529810083235559, -336586431913944092]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-429663236730267840275727460931813828, -47325199233162760539807962973973197, -23399923187028870566419090765918438]] ![![-224731223638518460, -21587748524932182, 38757676331322499]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8582588, 945328, 467417]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![8582588, 945328, 467417]] 
 ![![211, 0, 0], ![0, 211, 0], ![64, 147, 1]] where
  M :=![![![8582588, 945328, 467417], ![69624145, 7668742, 3791806], ![88545144, 9752793, 4822264]]]
  hmulB := by decide  
  f := ![![![-2570, 299, 14]], ![![1544, -2056, 1467]], ![![505, -1348, 1011]]]
  g := ![![![-101100, -321161, 467417], ![-820149, -2605340, 3791806], ![-1043032, -3313365, 4822264]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [185, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [132, 210], [0, 1]]
 g := ![![[70, 73], [104, 182], [134], [4], [41, 109], [171], [132, 1]], ![[0, 138], [74, 29], [134], [4], [81, 102], [171], [53, 210]]]
 h' := ![![[132, 210], [172, 101], [93, 155], [14, 150], [11, 2], [197, 113], [56, 148], [0, 1]], ![[0, 1], [0, 110], [86, 56], [191, 61], [64, 209], [132, 98], [180, 63], [132, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [51, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [185, 79, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3095771, 981804, -215250]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![79961, 154614, -215250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2570, -299, -14]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![2570, -299, -14]] 
 ![![211, 0, 0], ![111, 1, 0], ![23, 0, 1]] where
  M :=![![![2570, -299, -14], ![-1544, 2056, -1467], ![-44067, 1332, 3224]]]
  hmulB := by decide  
  f := ![![![-8582588, -945328, -467417]], ![![-4844983, -533650, -263863]], ![![-1355188, -149267, -73805]]]
  g := ![![![171, -299, -14], ![-929, 2056, -1467], ![-1261, 1332, 3224]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![8582588, 945328, 467417]] ![![2570, -299, -14]]
  ![![211, 0, 0]] where
 M := ![![![-211, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235847927449709311949, 31379387246070906336, -1813508857057320906]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-235847927449709311949, 31379387246070906336, -1813508857057320906]] 
 ![![223, 0, 0], ![102, 1, 0], ![108, 0, 1]] where
  M :=![![![-235847927449709311949, 31379387246070906336, -1813508857057320906], ![-340225629621911911290, -162208099815223573841, 160523953944469173492], ![5018667311495727178128, -248122115759317027914, -291352666513621840997]]]
  hmulB := by decide  
  f := ![![![87089305494025973973598603023705663415165, 9592439802267618527581528707375929627076, 4742977487392603610491667082007142025366]], ![![43002689849135347357206813966593356677012, 4736525470876693628605953300891298172551, 2341972859868154500838898438285174218260]], ![![46206865401859364980312210623084627079536, 5089448954776919322688524402953275824210, 2516475715597854315737977229317024999099]]]
  g := ![![![-14532226322810543051, 31379387246070906336, -1813508857057320906], ![-5074378809290484828, -162208099815223573841, 160523953944469173492], ![277099601356131044184, -248122115759317027914, -291352666513621840997]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![988722126671638950285917860387790499343, 108902665229295036317031676157288893448, 53846873177926585728806554879733617448]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![988722126671638950285917860387790499343, 108902665229295036317031676157288893448, 53846873177926585728806554879733617448]] 
 ![![223, 0, 0], ![139, 1, 0], ![183, 0, 1]] where
  M :=![![![988722126671638950285917860387790499343, 108902665229295036317031676157288893448, 53846873177926585728806554879733617448], ![8020766265764177543873339544284665682648, 883446218062669508547141883423966581551, 436819579790622010127545271026977232344], ![10200482998730950269049059866497166603784, 1123530823495807111148426254087476015096, 555529303501342534736628288554278242655]]]
  hmulB := by decide  
  f := ![![![421754643763980792881, -46798077167046629432, -4082327246373219736]], ![![260506258156198748205, -27588700777180962505, -3557261069902978704]], ![![316192256824283126289, -37748773352903899824, -965855511223014713]]]
  g := ![![![-107635543191753077516381545598505012031, 108902665229295036317031676157288893448, 53846873177926585728806554879733617448], ![-873167000657536825100987295289612209291, 883446218062669508547141883423966581551, 436819579790622010127545271026977232344], ![-1110458134564717139181099400256031021975, 1123530823495807111148426254087476015096, 555529303501342534736628288554278242655]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 4, 2]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![35, 4, 2]] 
 ![![223, 0, 0], ![205, 1, 0], ![165, 0, 1]] where
  M :=![![![35, 4, 2], ![298, 31, 16], ![372, 42, 19]]]
  hmulB := by decide  
  f := ![![![-83, 8, 2]], ![![-75, 7, 2]], ![![-57, 6, 1]]]
  g := ![![![-5, 4, 2], ![-39, 31, 16], ![-51, 42, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-235847927449709311949, 31379387246070906336, -1813508857057320906]] ![![988722126671638950285917860387790499343, 108902665229295036317031676157288893448, 53846873177926585728806554879733617448]]
  ![![-83, 8, 2]] where
 M := ![![![-83, 8, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-83, 8, 2]] ![![35, 4, 2]]
  ![![223, 0, 0]] where
 M := ![![![223, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)


lemma PB225I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 224 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 224 (by omega)

def PB225I4 : PrimesBelowBoundCertificateInterval O 193 224 225 where
  m := 4
  g := ![2, 2, 2, 3]
  P := ![197, 199, 211, 223]
  hP := PB225I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
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
      exact NI223N1
      exact NI223N2
  β := ![I197N1, I199N1, I211N1, I223N0, I223N1, I223N2]
  Il := ![[I197N1], [I199N1], [I211N1], [I223N0, I223N1, I223N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
