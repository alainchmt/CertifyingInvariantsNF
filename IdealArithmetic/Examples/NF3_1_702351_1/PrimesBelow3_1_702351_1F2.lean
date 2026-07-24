
import IdealArithmetic.Examples.NF3_1_702351_1.RI3_1_702351_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [76, 22, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 72, 37], [30, 10, 46], [0, 1]]
 g := ![![[66, 27, 11], [26, 13, 11], [82, 3], [39, 37], [14, 77, 1], []], ![[69, 30, 29, 70], [7, 27, 36, 81], [23, 59], [3, 10], [29, 14, 44, 48], [19, 41]], ![[80, 49, 72, 20], [36, 68, 40, 2], [56, 4], [80, 69], [25, 52, 53, 5], [10, 41]]]
 h' := ![![[47, 72, 37], [16, 66, 29], [76, 43, 54], [0, 23, 13], [15, 65, 55], [0, 0, 1], [0, 1]], ![[30, 10, 46], [71, 17, 76], [81, 29, 56], [70, 40, 68], [76, 33, 50], [18, 80, 10], [47, 72, 37]], ![[0, 1], [80, 0, 61], [45, 11, 56], [20, 20, 2], [37, 68, 61], [57, 3, 72], [30, 10, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 46], []]
 b := ![[], [54, 18, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [76, 22, 6, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1279113, -6806, -23821]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15411, -82, -287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48378647218, -4025367609, -434402736]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![48378647218, -4025367609, -434402736]] 
 ![![89, 0, 0], ![0, 89, 0], ![10, 30, 1]] where
  M :=![![![48378647218, -4025367609, -434402736], ![-77989575714, 44353279609, -27743170527], ![-628101659193, -9991262928, 52404014827]]]
  hmulB := by decide  
  f := ![![![23001130461399049883, 2418939953013259659, 1471276921607549103]], ![![241713464284841924901, 25420070414412309542, 15461302749485268510]], ![![87676245249443098789, 9220571698421073171, 5608247665269880186]]]
  g := ![![![592389602, 101199039, -434402736], ![2240922804, 9849981971, -27743170527], ![-12945413567, -17776536042, 52404014827]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [78, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 88], [0, 1]]
 g := ![![[66, 8], [17], [84], [81, 40], [26, 18], [1]], ![[0, 81], [17], [84], [18, 49], [11, 71], [1]]]
 h' := ![![[14, 88], [77, 39], [35, 62], [1, 66], [19, 60], [11, 14], [0, 1]], ![[0, 1], [0, 50], [13, 27], [35, 23], [58, 29], [29, 75], [14, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [72, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [78, 75, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14426, 7452, 1530]
  a := ![5, 0, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-334, -432, 1530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23001130461399049883, -2418939953013259659, -1471276921607549103]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-23001130461399049883, -2418939953013259659, -1471276921607549103]] 
 ![![89, 0, 0], ![58, 1, 0], ![20, 0, 1]] where
  M :=![![![-23001130461399049883, -2418939953013259659, -1471276921607549103], ![-241713464284841924901, -25420070414412309542, -15461302749485268510], ![-321770594041187546361, -33839369196973629369, -20582190508385790224]]]
  hmulB := by decide  
  f := ![![![-48378647218, 4025367609, 434402736]], ![![-30651370370, 2124921817, 594814935]], ![![-3814284103, 1016838372, -491190563]]]
  g := ![![![1648572193769898791, -2418939953013259659, -1471276921607549103], ![17324457019559296615, -25420070414412309542, -15461302749485268510], ![23062434039898862489, -33839369196973629369, -20582190508385790224]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![48378647218, -4025367609, -434402736]] ![![-23001130461399049883, -2418939953013259659, -1471276921607549103]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42383730, -4457333, -2711093]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-42383730, -4457333, -2711093]] 
 ![![97, 0, 0], ![0, 97, 0], ![38, 7, 1]] where
  M :=![![![-42383730, -4457333, -2711093], ![-445400639, -46841063, -28490238], ![-592920335, -62355139, -37926397]]]
  hmulB := by decide  
  f := ![![![-6257, 642, -35]], ![![-4351, -5615, 4529]], ![![-1683, -162, 242]]]
  g := ![![![625132, 149694, -2711093], ![6569365, 1573099, -28490238], ![8745183, 2094120, -37926397]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [86, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 96], [0, 1]]
 g := ![![[8, 44], [4], [73], [24], [25], [88, 1]], ![[0, 53], [4], [73], [24], [25], [79, 96]]]
 h' := ![![[88, 96], [13, 23], [39, 2], [20, 48], [85, 86], [95, 92], [0, 1]], ![[0, 1], [0, 74], [21, 95], [73, 49], [87, 11], [43, 5], [88, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [17, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [86, 9, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2291386, 922791, 27677]
  a := ![-66, -64, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12780, 7516, 27677]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6257, 642, -35]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-6257, 642, -35]] 
 ![![97, 0, 0], ![49, 1, 0], ![66, 0, 1]] where
  M :=![![![-6257, 642, -35], ![-4351, -5615, 4529], ![104972, -805, -6899]]]
  hmulB := by decide  
  f := ![![![-42383730, -4457333, -2711093]], ![![-26002097, -2734540, -1663235]], ![![-34950995, -3675661, -2235655]]]
  g := ![![![-365, 642, -35], ![-290, -5615, 4529], ![6183, -805, -6899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-42383730, -4457333, -2711093]] ![![-6257, 642, -35]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-233796435, -28491958, 38115578]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-233796435, -28491958, 38115578]] 
 ![![101, 0, 0], ![0, 101, 0], ![30, 15, 1]] where
  M :=![![![-233796435, -28491958, 38115578], ![6079624142, -262288393, -237559284], ![-6340521826, 876658294, -205304477]]]
  hmulB := by decide  
  f := ![![![2595121762211257, 272918921271366, 165998047961626]], ![![27271523564364518, 2868040683482623, 1744434400937936]], ![![5180500420299610, 544813197955423, 331372874196611]]]
  g := ![![![-13636275, -5942828, 38115578], ![130756462, 32684167, -237559284], ![-1795916, 39170549, -205304477]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [89, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 100], [0, 1]]
 g := ![![[64, 80], [58], [21, 19], [14], [16], [61, 1]], ![[96, 21], [58], [69, 82], [14], [16], [21, 100]]]
 h' := ![![[61, 100], [65, 22], [50, 82], [47, 76], [9, 69], [25, 97], [0, 1]], ![[0, 1], [94, 79], [2, 19], [37, 25], [77, 32], [84, 4], [61, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [24, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [89, 40, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9192, 7423, -569]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, 158, -569]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2595121762211257, -272918921271366, -165998047961626]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-2595121762211257, -272918921271366, -165998047961626]] 
 ![![101, 0, 0], ![98, 1, 0], ![86, 0, 1]] where
  M :=![![![-2595121762211257, -272918921271366, -165998047961626], ![-27271523564364518, -2868040683482623, -1744434400937936], ![-36304036118455130, -3817955103117398, -2322202840939891]]]
  hmulB := by decide  
  f := ![![![233796435, 28491958, -38115578]], ![![166657688, 30242577, -34631360]], ![![261851636, 15580694, -30422131]]]
  g := ![![![380463016307747, -272918921271366, -165998047961626], ![3998196256411832, -2868040683482623, -1744434400937936], ![5322425824830500, -3817955103117398, -2322202840939891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-233796435, -28491958, 38115578]] ![![-2595121762211257, -272918921271366, -165998047961626]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10671809684, 247104492, 577228645]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-10671809684, 247104492, 577228645]] 
 ![![103, 0, 0], ![0, 103, 0], ![22, 71, 1]] where
  M :=![![![-10671809684, 247104492, 577228645], ![93428020829, -10424705192, 1152502799], ![13231305542, 13276258835, -10918914176]]]
  hmulB := by decide  
  f := ![![![-956558600329743909, -100597569307266089, -61186670593962116]], ![![-10052249104242432854, -1057156169637009998, -642996314556900507]], ![![-7263452402132181375, -763869203812123228, -464609768132326023]]]
  g := ![![![-226901358, -395496401, 577228645], ![660902517, -895654407, 1152502799], ![2460654538, 7655525877, -10918914176]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [85, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 102], [0, 1]]
 g := ![![[53, 4], [35, 34], [58, 8], [68], [58], [27, 1]], ![[58, 99], [26, 69], [68, 95], [68], [58], [54, 102]]]
 h' := ![![[27, 102], [12, 2], [14, 31], [22, 76], [31, 58], [74, 26], [0, 1]], ![[0, 1], [66, 101], [27, 72], [14, 27], [52, 45], [55, 77], [27, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [66, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [85, 76, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2199, 987, -504]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![129, 357, -504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![956558600329743909, 100597569307266089, 61186670593962116]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![956558600329743909, 100597569307266089, 61186670593962116]] 
 ![![103, 0, 0], ![19, 1, 0], ![49, 0, 1]] where
  M :=![![![956558600329743909, 100597569307266089, 61186670593962116], ![10052249104242432854, 1057156169637009998, 642996314556900507], ![13381621811147582993, 1407293423661128668, 855961031022477820]]]
  hmulB := by decide  
  f := ![![![10671809684, -247104492, -577228645]], ![![1061518089, 55628348, -117668418]], ![![4948421058, -246450281, -168595043]]]
  g := ![![![-38378078404004422, 100597569307266089, 61186670593962116], ![-403306189632513417, 1057156169637009998, 642996314556900507], ![-536883919985585193, 1407293423661128668, 855961031022477820]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-10671809684, 247104492, 577228645]] ![![956558600329743909, 100597569307266089, 61186670593962116]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49211, -417, 3831]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-49211, -417, 3831]] 
 ![![107, 0, 0], ![0, 107, 0], ![76, 81, 1]] where
  M :=![![![-49211, -417, 3831], ![615957, -49628, -6750], ![-243363, 88113, -48794]]]
  hmulB := by decide  
  f := ![![![28189826, 2964615, 1803174]], ![![296240244, 31154441, 18949131]], ![![247964893, 26077509, 15861178]]]
  g := ![![![-3181, -2904, 3831], ![10551, 4646, -6750], ![32383, 37761, -48794]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [13, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 106], [0, 1]]
 g := ![![[54, 33], [79, 90], [35], [16, 36], [33], [47, 1]], ![[0, 74], [29, 17], [35], [103, 71], [33], [94, 106]]]
 h' := ![![[47, 106], [43, 56], [9, 25], [6, 79], [104, 101], [31, 56], [0, 1]], ![[0, 1], [0, 51], [7, 82], [81, 28], [36, 6], [95, 51], [47, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [72, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [13, 60, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64104, 4127, 3327]
  a := ![3, 21, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1764, -2480, 3327]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28189826, 2964615, 1803174]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![28189826, 2964615, 1803174]] 
 ![![107, 0, 0], ![76, 1, 0], ![5, 0, 1]] where
  M :=![![![28189826, 2964615, 1803174], ![296240244, 31154441, 18949131], ![394357011, 41473002, 25225211]]]
  hmulB := by decide  
  f := ![![![-49211, -417, 3831]], ![![-29197, -760, 2658]], ![![-4574, 804, -277]]]
  g := ![![![-1926512, 2964615, 1803174], ![-20245261, 31154441, 18949131], ![-26950628, 41473002, 25225211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-49211, -417, 3831]] ![![28189826, 2964615, 1803174]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [23, 91, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 72, 48], [15, 36, 61], [0, 1]]
 g := ![![[20, 54, 89], [86, 60], [4, 12, 66], [21, 20, 100], [37, 81], [1]], ![[70, 80, 106, 66], [77, 104], [95, 10, 35, 78], [80, 77, 9, 66], [107, 25], [75, 11, 30, 66]], ![[37, 87, 71, 73], [47, 88], [52, 26, 98, 22], [84, 88, 86, 12], [35, 87], [80, 37, 34, 43]]]
 h' := ![![[85, 72, 48], [55, 104, 78], [17, 43, 96], [62, 52, 75], [5, 46, 10], [86, 18, 100], [0, 1]], ![[15, 36, 61], [8, 49, 61], [12, 103, 70], [83, 33, 73], [73, 5, 61], [38, 54, 104], [85, 72, 48]], ![[0, 1], [8, 65, 79], [76, 72, 52], [64, 24, 70], [39, 58, 38], [9, 37, 14], [15, 36, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 37], []]
 b := ![[], [101, 4, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [23, 91, 9, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3683437, -11663, 116630]
  a := ![-3, 1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33793, -107, 1070]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [94, 39, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 106, 1], [2, 6, 112], [0, 1]]
 g := ![![[60, 79, 72], [61, 83], [51, 52], [69, 62], [102, 1, 31], [1]], ![[20, 102, 12, 15], [82, 98], [12, 25], [94, 88], [105, 59, 29, 72], [80, 30, 104, 1]], ![[59, 51, 89, 60], [112, 16], [71, 15], [33, 106], [111, 64, 9, 9], [112, 9, 6, 112]]]
 h' := ![![[10, 106, 1], [43, 72, 33], [50, 11, 14], [18, 3, 74], [17, 18, 66], [19, 74, 12], [0, 1]], ![[2, 6, 112], [97, 111, 44], [11, 112, 95], [3, 74, 108], [108, 87, 75], [34, 96, 33], [10, 106, 1]], ![[0, 1], [93, 43, 36], [15, 103, 4], [94, 36, 44], [91, 8, 85], [102, 56, 68], [2, 6, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 88], []]
 b := ![[], [25, 101, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [94, 39, 101, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10725169, 533473, 105203]
  a := ![4, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![94913, 4721, 931]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6880, 373, -772]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![6880, 373, -772]] 
 ![![127, 0, 0], ![0, 127, 0], ![74, 77, 1]] where
  M :=![![![6880, 373, -772], ![-123546, 7253, 3383], ![95565, -17756, 6507]]]
  hmulB := by decide  
  f := ![![![844597, 88823, 54025]], ![![8875671, 933420, 567736]], ![![5966474, 627471, 381648]]]
  g := ![![![504, 471, -772], ![-2944, -1994, 3383], ![-3039, -4085, 6507]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [37, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 126], [0, 1]]
 g := ![![[121, 103], [122, 107], [114, 32], [120, 18], [47, 79], [95, 1]], ![[0, 24], [0, 20], [106, 95], [52, 109], [59, 48], [63, 126]]]
 h' := ![![[95, 126], [58, 105], [100, 19], [5, 63], [39, 48], [41, 98], [0, 1]], ![[0, 1], [0, 22], [0, 108], [21, 64], [27, 79], [80, 29], [95, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [22, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [37, 32, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13752, 5090, -305]
  a := ![-5, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![286, 225, -305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![844597, 88823, 54025]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![844597, 88823, 54025]] 
 ![![127, 0, 0], ![97, 1, 0], ![3, 0, 1]] where
  M :=![![![844597, 88823, 54025], ![8875671, 933420, 567736], ![11815353, 1242575, 755774]]]
  hmulB := by decide  
  f := ![![![6880, 373, -772]], ![![4282, 342, -563]], ![![915, -131, 33]]]
  g := ![![![-62467, 88823, 54025], ![-656451, 933420, 567736], ![-873872, 1242575, 755774]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![6880, 373, -772]] ![![844597, 88823, 54025]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, -8, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![71, -8, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![71, 123, 1]] where
  M :=![![![71, -8, 1], ![145, 63, -57], ![-1334, 23, 79]]]
  hmulB := by decide  
  f := ![![![48, 5, 3]], ![![493, 53, 32]], ![![494, 53, 32]]]
  g := ![![![0, -1, 1], ![32, 54, -57], ![-53, -74, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [87, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 130], [0, 1]]
 g := ![![[34, 89], [29, 129], [20], [89], [4], [12], [1]], ![[82, 42], [50, 2], [20], [89], [4], [12], [1]]]
 h' := ![![[55, 130], [97, 58], [75, 28], [80, 85], [15, 58], [106, 129], [44, 55], [0, 1]], ![[0, 1], [12, 73], [43, 103], [39, 46], [61, 73], [127, 2], [56, 76], [55, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [86, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [87, 76, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56389, 8708, 2252]
  a := ![6, -6, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1651, -2048, 2252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48, 5, 3]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![48, 5, 3]] 
 ![![131, 0, 0], ![57, 1, 0], ![52, 0, 1]] where
  M :=![![![48, 5, 3], ![493, 53, 32], ![667, 69, 43]]]
  hmulB := by decide  
  f := ![![![71, -8, 1]], ![![32, -3, 0]], ![![18, -3, 1]]]
  g := ![![![-3, 5, 3], ![-32, 53, 32], ![-42, 69, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![71, -8, 1]] ![![48, 5, 3]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2036153674074, 214134408783, 130243420624]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![2036153674074, 214134408783, 130243420624]] 
 ![![137, 0, 0], ![0, 137, 0], ![69, 62, 1]] where
  M :=![![![2036153674074, 214134408783, 130243420624], ![21397459538030, 2250288082857, 1368697440857], ![28484442465359, 2995598674352, 1822019265291]]]
  hmulB := by decide  
  f := ![![![-369221, 140035, -78801]], ![![-12406891, -229186, 1059046]], ![![-5609730, -46420, 435871]]]
  g := ![![![-50734615686, -57379253065, 130243420624], ![-533158130519, -602985060221, 1368697440857], ![-709743699560, -802697779370, 1822019265291]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [13, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 136], [0, 1]]
 g := ![![[55, 74], [28], [133], [16, 68], [69], [78], [1]], ![[27, 63], [28], [133], [31, 69], [69], [78], [1]]]
 h' := ![![[107, 136], [75, 38], [24, 24], [66, 74], [43, 94], [114, 84], [124, 107], [0, 1]], ![[0, 1], [31, 99], [126, 113], [38, 63], [100, 43], [60, 53], [65, 30], [107, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [41, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [13, 30, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![96246, 49617, 2747]
  a := ![15, 13, 46]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-681, -881, 2747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-369221, 140035, -78801]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-369221, 140035, -78801]] 
 ![![137, 0, 0], ![115, 1, 0], ![130, 0, 1]] where
  M :=![![![-369221, 140035, -78801], ![-12406891, -229186, 1059046], ![26170481, -1812423, -509256]]]
  hmulB := by decide  
  f := ![![![2036153674074, 214134408783, 130243420624]], ![![1865365927420, 196173321846, 119318911041]], ![![2140032263467, 225058918366, 136888058003]]]
  g := ![![![-45468, 140035, -78801], ![-903113, -229186, 1059046], ![2195638, -1812423, -509256]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![2036153674074, 214134408783, 130243420624]] ![![-369221, 140035, -78801]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB238I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB238I2 : PrimesBelowBoundCertificateInterval O 79 137 238 where
  m := 11
  g := ![1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB238I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I97N1, I101N1, I103N1, I107N1, I127N1, I131N1, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
