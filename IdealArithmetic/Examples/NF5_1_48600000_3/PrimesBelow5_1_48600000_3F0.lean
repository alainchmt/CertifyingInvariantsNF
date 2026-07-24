
import IdealArithmetic.Examples.NF5_1_48600000_3.RI5_1_48600000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 4, -4, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![4, 4, -4, 1, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![4, 4, -4, 1, 0], ![0, 4, 0, -10, 3], ![6, 15, 1, 2, -27], ![-30, -72, 21, 79, 3], ![-18, -53, -4, 8, 82]]]
  hmulB := by decide  
  f := ![![![-1039, -3188, -3103, -221, -897]], ![![-897, -2762, -2697, -191, -780]], ![![-1560, -4797, -4679, -332, -1353]], ![![-573, -1764, -1722, -122, -498]], ![![-714, -2197, -2144, -152, -620]]]
  g := ![![![2, 4, -4, 1, 0], ![0, 4, 0, -10, 3], ![3, 15, 1, 2, -27], ![-15, -72, 21, 79, 3], ![-9, -53, -4, 8, 82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, 1, -1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-1, -1, 1, 1, -1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 1, 1, -1], ![-2, -6, 1, 6, 2], ![4, 8, -7, -22, 20], ![18, 48, -6, -34, -33], ![-10, -17, 21, 62, -67]]]
  hmulB := by decide  
  f := ![![![36, 89, 53, 8, 14]], ![![14, 53, 64, 3, 19]], ![![38, 109, 98, 8, 28]], ![![27, 79, 67, 6, 19]], ![![14, 46, 48, 3, 14]]]
  g := ![![![-1, -1, 1, 1, -1], ![-4, -6, 1, 6, 2], ![13, 8, -7, -22, 20], ![26, 48, -6, -34, -33], ![-36, -17, 21, 62, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, -155, 119, -24, 45]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-125, -155, 119, -24, 45]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-125, -155, 119, -24, 45], ![90, 100, -81, 16, -27], ![-54, -45, 46, -32, 21], ![48, 48, -33, 31, -48], ![0, -32, -1, 74, -17]]]
  hmulB := by decide  
  f := ![![![-330676, -1017197, -992440, -70386, -286989]], ![![-452327, -1391409, -1357544, -96280, -392568]], ![![-663485, -2040955, -1991281, -141226, -575829]], ![![-348599, -1072330, -1046231, -74201, -302544]], ![![-393545, -1210589, -1181125, -83768, -341552]]]
  g := ![![![-55, -155, 119, -24, 45], ![41, 100, -81, 16, -27], ![-22, -45, 46, -32, 21], ![25, 48, -33, 31, -48], ![-12, -32, -1, 74, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![4, 4, -4, 1, 0]] ![![-1, -1, 1, 1, -1]]
  ![![-10, -12, 30, 82, -109]] where
 M := ![![![-10, -12, 30, 82, -109]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-10, -12, 30, 82, -109]] ![![-1, -1, 1, 1, -1]]
  ![![2720, 6111, -3013, -10288, 5183]] where
 M := ![![![2720, 6111, -3013, -10288, 5183]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2720, 6111, -3013, -10288, 5183]] ![![-125, -155, 119, -24, 45]]
  ![![-121132, -334595, 24412, 193526, 299843]] where
 M := ![![![-121132, -334595, 24412, 193526, 299843]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-121132, -334595, 24412, 193526, 299843]] ![![-125, -155, 119, -24, 45]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-7001050, -16088308, 7124238, 24960152, -10290802]]]
 hmul := by decide  
 g := ![![![![-3500525, -8044154, 3562119, 12480076, -5145401]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-169939, -522745, -510020, -36172, -147485]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-169939, -522745, -510020, -36172, -147485]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-169939, -522745, -510020, -36172, -147485], ![-294970, -907364, -885280, -62786, -256001], ![-512002, -1574975, -1536643, -108982, -444359], ![-188358, -579411, -565308, -40093, -163473], ![-234554, -721515, -703954, -49926, -203566]]]
  hmulB := by decide  
  f := ![![![39, 101, -26, -104, -15]], ![![-10, -12, 30, 82, -109]], ![![-218, -555, 127, 550, 137]], ![![246, 511, -346, -1109, 825]], ![![740, 1865, -468, -1950, -294]]]
  g := ![![![41677, -522745, -510020, -36172, -147485], ![72344, -907364, -885280, -62786, -256001], ![125572, -1574975, -1536643, -108982, -444359], ![46196, -579411, -565308, -40093, -163473], ![57526, -721515, -703954, -49926, -203566]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 36, -26, 6, -10]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![23, 36, -26, 6, -10]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![23, 36, -26, 6, -10], ![-20, -27, 20, -4, 8], ![16, 20, -15, 0, -4], ![-12, -12, 12, -3, 0], ![-8, -12, 8, 8, -3]]]
  hmulB := by decide  
  f := ![![![573, 1764, 1722, 122, 498]], ![![714, 2197, 2144, 152, 620]], ![![958, 2948, 2877, 204, 832]], ![![212, 652, 636, 45, 184]], ![![264, 812, 792, 56, 229]]]
  g := ![![![1, 36, -26, 6, -10], ![-2, -27, 20, -4, 8], ![2, 20, -15, 0, -4], ![-4, -12, 12, -3, 0], ![0, -12, 8, 8, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-169939, -522745, -510020, -36172, -147485]] ![![-169939, -522745, -510020, -36172, -147485]]
  ![![485611098677, 1493794600702, 1457437621906, 103364680824, 421454750206]] where
 M := ![![![485611098677, 1493794600702, 1457437621906, 103364680824, 421454750206]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![485611098677, 1493794600702, 1457437621906, 103364680824, 421454750206]] ![![23, 36, -26, 6, -10]]
  ![![151034491, 464599178, 453291384, 32148430, 131080604]] where
 M := ![![![151034491, 464599178, 453291384, 32148430, 131080604]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![151034491, 464599178, 453291384, 32148430, 131080604]] ![![23, 36, -26, 6, -10]]
  ![![45885, 143142, 142026, 9776, 41166]] where
 M := ![![![45885, 143142, 142026, 9776, 41166]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![45885, 143142, 142026, 9776, 41166]] ![![23, 36, -26, 6, -10]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![18291, 16242, -13920, 2742, -5316]]]
 hmul := by decide  
 g := ![![![![6097, 5414, -4640, 914, -1772]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2748953, 8456090, 8250280, 585128, 2385776]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![2748953, 8456090, 8250280, 585128, 2385776]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![2748953, 8456090, 8250280, 585128, 2385776], ![4771552, 14677833, 14320594, 1015648, 4141160], ![8282320, 25477352, 24857267, 1762932, 7188104], ![3046944, 9372744, 9144624, 648557, 2644398], ![3794228, 11671474, 11387406, 807620, 3292955]]]
  hmulB := by decide  
  f := ![![![3981, 6398, -4588, 1032, -1744]], ![![1691, 2891, -2042, 464, -776]], ![![1337, 1934, -1425, 316, -544]], ![![1923, 3294, -2328, 533, -882]], ![![2984, 4874, -3482, 780, -1317]]]
  g := ![![![-8433617, 8456090, 8250280, 585128, 2385776], ![-14638825, 14677833, 14320594, 1015648, 4141160], ![-25409643, 25477352, 24857267, 1762932, 7188104], ![-9347835, 9372744, 9144624, 648557, 2644398], ![-11640456, 11671474, 11387406, 807620, 3292955]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![2748953, 8456090, 8250280, 585128, 2385776]] ![![2748953, 8456090, 8250280, 585128, 2385776]]
  ![![127071905147249, 390887535990356, 381373851947988, 27047872161680, 110283842747072]] where
 M := ![![![127071905147249, 390887535990356, 381373851947988, 27047872161680, 110283842747072]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![127071905147249, 390887535990356, 381373851947988, 27047872161680, 110283842747072]] ![![2748953, 8456090, 8250280, 585128, 2385776]]
  ![![5873970576360296111305, 18068997095878004416782, 17629221678385824483532, 1250303165335855968776, 5097932911240932864336]] where
 M := ![![![5873970576360296111305, 18068997095878004416782, 17629221678385824483532, 1250303165335855968776, 5097932911240932864336]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5873970576360296111305, 18068997095878004416782, 17629221678385824483532, 1250303165335855968776, 5097932911240932864336]] ![![2748953, 8456090, 8250280, 585128, 2385776]]
  ![![271527607081709687192322026721, 835249594806478823401849250728, 814920727779875069683960463592, 57795969897536058040750009152, 235654827762187770031618917856]] where
 M := ![![![271527607081709687192322026721, 835249594806478823401849250728, 814920727779875069683960463592, 57795969897536058040750009152, 235654827762187770031618917856]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![271527607081709687192322026721, 835249594806478823401849250728, 814920727779875069683960463592, 57795969897536058040750009152, 235654827762187770031618917856]] ![![2748953, 8456090, 8250280, 585128, 2385776]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![12551516976307893904784439614492323065, 38609884207880958066888857826756254530, 37670170849317240794171976367044267760, 2671651347455082326253664952780225160, 10893277493937941547960619179304629520]]]
 hmul := by decide  
 g := ![![![![2510303395261578780956887922898464613, 7721976841576191613377771565351250906, 7534034169863448158834395273408853552, 534330269491016465250732990556045032, 2178655498787588309592123835860925904]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [4, 2, 3, 2, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4, 2, 2, 4], [0, 3, 6, 2, 2], [4, 4, 4, 2, 2], [2, 2, 2, 1, 6], [0, 1]]
 g := ![![[5, 0, 1], []], ![[0, 1, 0, 3, 2, 6, 5, 1], [2, 0, 6, 4, 3, 2, 5, 1]], ![[6, 1, 5, 6, 4, 5, 6, 4], [1, 1, 0, 0, 4, 3, 3, 1]], ![[4, 1, 4, 1, 4, 2], [4, 3, 3, 4, 3, 0, 3, 1]], ![[1, 5, 4, 1, 5, 6, 5, 6], [3, 6, 2, 6, 6, 5, 3, 6]]]
 h' := ![![[1, 4, 2, 2, 4], [0, 0, 0, 1], [0, 1]], ![[0, 3, 6, 2, 2], [0, 1, 3, 2, 4], [1, 4, 2, 2, 4]], ![[4, 4, 4, 2, 2], [3, 1, 2, 1, 4], [0, 3, 6, 2, 2]], ![[2, 2, 2, 1, 6], [6, 4, 4, 1], [4, 4, 4, 2, 2]], ![[0, 1], [3, 1, 5, 2, 6], [2, 2, 2, 1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 6, 2, 3], [], [], []]
 b := ![[], [2, 2, 4, 6, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [4, 2, 3, 2, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3406732909482, -7366448931247, 4277676112969, 14099630239814, -8928208172464]
  a := ![0, -1, -4, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-486676129926, -1052349847321, 611096587567, 2014232891402, -1275458310352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -21, 18, -4, 7]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-23, -21, 18, -4, 7]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![6, 3, 1, 0, 0], ![10, 8, 0, 1, 0], ![9, 8, 0, 0, 1]] where
  M :=![![![-23, -21, 18, -4, 7], ![14, 12, -10, 2, -5], ![-10, -11, 7, 6, 1], ![6, 3, -6, -5, 9], ![10, 19, -8, -22, 4]]]
  hmulB := by decide  
  f := ![![![75, 225, 212, 16, 61]], ![![122, 380, 376, 26, 109]], ![![94, 287, 277, 20, 80]], ![![164, 503, 488, 35, 141]], ![![159, 488, 474, 34, 137]]]
  g := ![![![-14, -9, 18, -4, 7], ![9, 6, -10, 2, -5], ![-11, -8, 7, 6, 1], ![1, -1, -6, -5, 9], ![22, 17, -8, -22, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[2, 5], [3, 5], [1]], ![[0, 6], [1, 6], [1]]]
 h' := ![![[4, 10], [6, 4], [2, 4], [0, 1]], ![[0, 1], [0, 7], [7, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [2, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125, -159, -716, -1954, 3447]
  a := ![1, -3, -2, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-642, -905, -716, -1954, 3447]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![249, 790, 783, 54, 227]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![249, 790, 783, 54, 227]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 5, 1, 0, 0], ![2, 3, 0, 1, 0], ![2, 5, 0, 0, 1]] where
  M :=![![![249, 790, 783, 54, 227], ![454, 1384, 1346, 96, 389], ![778, 2399, 2341, 166, 677], ![288, 882, 861, 61, 249], ![358, 1099, 1072, 76, 310]]]
  hmulB := by decide  
  f := ![![![-1, -2, -1, 8, -1]], ![![-2, -6, -2, -12, 23]], ![![3, 7, -4, -14, 9]], ![![-4, -8, 5, 15, -10]], ![![-14, -35, 8, 32, 11]]]
  g := ![![![-242, -402, 783, 54, 227], ![-414, -689, 1346, 96, 389], ![-721, -1199, 2341, 166, 677], ![-265, -441, 861, 61, 249], ![-330, -549, 1072, 76, 310]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 10], [0, 1]]
 g := ![![[0, 4], [], [1]], ![[0, 7], [], [1]]]
 h' := ![![[0, 10], [0, 9], [8], [0, 1]], ![[0, 1], [0, 2], [8], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [3, 0, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3030, 5812, -4320, -15449, 15073]
  a := ![1, 19, 3, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1522, -146, -4320, -15449, 15073]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![-1, -1, 1, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 1, 0, 0], ![0, -1, 0, 2, 0], ![0, 0, -1, -4, 6], ![6, 15, -3, -13, -6], ![0, 2, 4, 10, -19]]]
  hmulB := by decide  
  f := ![![![97, 113, -77, 18, -30]], ![![21, 26, -15, 4, -6]], ![![22, 26, -15, 4, -6]], ![![59, 70, -46, 11, -18]], ![![43, 51, -33, 8, -13]]]
  g := ![![![0, -1, 1, 0, 0], ![-1, -1, 0, 2, 0], ![0, 0, -1, -4, 6], ![8, 15, -3, -13, -6], ![1, 2, 4, 10, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-23, -21, 18, -4, 7]] ![![249, 790, 783, 54, 227]]
  ![![97, 113, -77, 18, -30]] where
 M := ![![![97, 113, -77, 18, -30]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![97, 113, -77, 18, -30]] ![![-1, -1, 1, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-883, -1936, 1032, 3444, -1944]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-883, -1936, 1032, 3444, -1944]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![2, 7, 12, 1, 0], ![7, 10, 5, 0, 1]] where
  M :=![![![-883, -1936, 1032, 3444, -1944], ![-3888, -10603, 1040, 6840, 8388], ![16776, 38052, -17951, -61928, 28908], ![20520, 61632, 4572, -11783, -92892], ![-48248, -106892, 56080, 188832, -104675]]]
  hmulB := by decide  
  f := ![![![113514401, 349183120, 340684456, 24162092, 98517480]], ![![197034960, 606101801, 591350096, 41939848, 171003756]], ![![342007512, 1052053740, 1026448141, 72797960, 296823300]], ![![448937170, 1380981451, 1347370192, 95558457, 389625984]], ![![356281971, 1095963594, 1069289293, 75836348, 309211897]]]
  g := ![![![449, -508, -2352, 3444, -1944], ![-5868, -10951, -9460, 6840, 8388], ![-4748, 14036, 44665, -61928, 28908], ![53410, 82541, 46956, -11783, -92892], ![23601, -29382, -129733, 188832, -104675]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [7, 11, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 8, 11], [10, 4, 2], [0, 1]]
 g := ![![[3, 4, 9], [3, 4], [1]], ![[2, 10, 10, 2], [3, 3], [5, 2, 2, 5]], ![[0, 11, 0, 8], [7, 10], [10, 9, 12, 8]]]
 h' := ![![[5, 8, 11], [2, 2, 3], [6, 2, 2], [0, 1]], ![[10, 4, 2], [6, 2, 8], [12, 11, 4], [5, 8, 11]], ![[0, 1], [0, 9, 2], [7, 0, 7], [10, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 9], []]
 b := ![[], [8, 10, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [7, 11, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5012260, -10850484, 6270566, 20691733, -13033696]
  a := ![-1, 0, -2, 9, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3449242, -1950435, -13604750, 20691733, -13033696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113514401, 349183120, 340684456, 24162092, 98517480]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![113514401, 349183120, 340684456, 24162092, 98517480]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![10, 3, 1, 0, 0], ![6, 12, 0, 1, 0], ![3, 11, 0, 0, 1]] where
  M :=![![![113514401, 349183120, 340684456, 24162092, 98517480], ![197034960, 606101801, 591350096, 41939848, 171003756], ![342007512, 1052053740, 1026448141, 72797960, 296823300], ![125819544, 387035136, 377615220, 26781301, 109196940], ![156677656, 481958172, 470227952, 33349600, 135978241]]]
  hmulB := by decide  
  f := ![![![-883, -1936, 1032, 3444, -1944]], ![![-3888, -10603, 1040, 6840, 8388]], ![![-286, -1009, -347, -536, 2664]], ![![-2418, -5940, 1788, 6997, -300]], ![![-7205, -17641, 5432, 21108, -1403]]]
  g := ![![![-287219627, -157423664, 340684456, 24162092, 98517480], ![-498547412, -273251383, 591350096, 41939848, 171003756], ![-865363966, -474301731, 1026448141, 72797960, 296823300], ![-318354714, -174488652, 377615220, 26781301, 109196940], ![-396433399, -217283195, 470227952, 33349600, 135978241]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12], [0, 1]]
 g := ![![[10, 1], [12], [3, 1]], ![[0, 12], [12], [6, 12]]]
 h' := ![![[3, 12], [10, 1], [10, 8], [0, 1]], ![[0, 1], [0, 12], [8, 5], [3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [11, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2503, -6512, 1384, 5672, 3224]
  a := ![0, 0, -6, -6, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4619, -8784, 1384, 5672, 3224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-883, -1936, 1032, 3444, -1944]] ![![113514401, 349183120, 340684456, 24162092, 98517480]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [15, 4, 8, 3, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 4, 16, 14, 9], [4, 16, 16, 14], [12, 2, 13, 15], [0, 11, 6, 8, 8], [0, 1]]
 g := ![![[15, 13, 3, 5, 13], [16, 5, 12, 1], [], []], ![[4, 0, 0, 6, 5, 8, 14, 16], [7, 7, 3, 8], [1, 9, 11, 4], [10, 3, 0, 13]], ![[5, 14, 7, 7, 13, 14, 5], [10, 2, 15, 1], [16, 1, 3, 8], [12, 9]], ![[11, 12, 16, 8, 5, 4, 8], [7, 10, 8, 1], [16, 15, 10, 1], [13, 4]], ![[0, 6, 5, 16, 4, 10, 6, 13], [3, 11, 8, 16], [11, 3, 11, 4], [14, 10, 12, 13]]]
 h' := ![![[13, 4, 16, 14, 9], [15, 14, 12, 2, 9], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[4, 16, 16, 14], [16, 12, 3, 15, 7], [6, 5, 16, 11, 12], [2, 2, 0, 5, 15], [13, 4, 16, 14, 9]], ![[12, 2, 13, 15], [3, 15, 6, 5, 15], [0, 9, 7, 10, 1], [6, 13, 14, 6, 5], [4, 16, 16, 14]], ![[0, 11, 6, 8, 8], [1, 9, 1, 14, 8], [15, 0, 1, 2, 16], [0, 4, 9, 1, 16], [12, 2, 13, 15]], ![[0, 1], [4, 1, 12, 15, 12], [7, 3, 10, 11, 4], [11, 15, 10, 5, 15], [0, 11, 6, 8, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 10, 16, 14], [], [], []]
 b := ![[], [15, 14, 3, 0, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [15, 4, 8, 3, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3005699798194, -7192083912486, 2556723184429, 9504802213979, -1991517189303]
  a := ![13, -1, -2, 7, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-176805870482, -423063759558, 150395481437, 559106012587, -117148069959]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6987065, 21492982, 20969860, 1487230, 6063962]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![6987065, 21492982, 20969860, 1487230, 6063962]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![7, 4, 11, 7, 1]] where
  M :=![![![6987065, 21492982, 20969860, 1487230, 6063962], ![12127924, 37306875, 36398880, 2581488, 10525652], ![21051304, 64756184, 63180103, 4480872, 18270116], ![7744464, 23822850, 23243034, 1648447, 6721308], ![9643848, 29665568, 28943548, 2052740, 8369755]]]
  hmulB := by decide  
  f := ![![![3, 14, 8, -14, -26]], ![![-52, -127, 48, 200, -68]], ![![-136, -392, -11, 104, 532]], ![![600, 1458, -462, -1763, 156]], ![![159, 364, -165, -585, 257]]]
  g := ![![![-1866351, -145414, -2407038, -2155816, 6063962], ![-3239560, -252407, -4178068, -3742004, 10525652], ![-5623132, -438120, -7252167, -6495260, 18270116], ![-2068668, -161178, -2667966, -2389511, 6721308], ![-2576023, -200708, -3322303, -2975555, 8369755]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [4, 12, 3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 15, 7, 2], [10, 3, 7, 14], [12, 0, 5, 3], [0, 1]]
 g := ![![[6, 11, 7, 5], [11, 18, 4, 4], [1], []], ![[10, 7, 10, 10, 7, 8], [12, 1, 18, 18, 14, 18], [2, 8, 17], [0, 1, 4]], ![[18, 14, 15, 5, 16, 15], [7, 1, 5, 18], [8, 4, 6], [13, 13, 6]], ![[3, 4, 16, 9, 14, 10], [0, 13, 6, 17, 1, 18], [2, 0, 1], [12, 12, 9]]]
 h' := ![![[14, 15, 7, 2], [13, 2, 2, 9], [15, 7, 16, 17], [0, 0, 1], [0, 1]], ![[10, 3, 7, 14], [3, 2, 16, 2], [9, 15, 9, 16], [6, 17, 13, 6], [14, 15, 7, 2]], ![[12, 0, 5, 3], [4, 18, 14, 4], [11, 6, 2], [10, 4, 6, 14], [10, 3, 7, 14]], ![[0, 1], [18, 16, 6, 4], [12, 10, 11, 5], [1, 17, 18, 18], [12, 0, 5, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 10, 14], []]
 b := ![[], [], [2, 7, 10, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [4, 12, 3, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![77989522, 174502272, -87623748, -297937068, 154574244]
  a := ![-1, -3, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-52843694, -23357616, -94102128, -72629304, 154574244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 14, 8, -14, -26]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![3, 14, 8, -14, -26]] 
 ![![19, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![3, 14, 8, -14, -26], ![-52, -127, 48, 200, -68], ![-136, -392, -11, 104, 532], ![600, 1458, -462, -1763, 156], ![504, 1432, -28, -620, -1607]]]
  hmulB := by decide  
  f := ![![![6987065, 21492982, 20969860, 1487230, 6063962]], ![![6522156, 20062873, 19574560, 1388272, 5660476]], ![![4785366, 14720316, 14362037, 1018588, 4153144]], ![![4085006, 12565930, 12260086, 869513, 3545312]], ![![1978532, 6086184, 5938052, 421140, 1717137]]]
  g := ![![![-3, 14, 8, -14, -26], ![-12, -127, 48, 200, -68], ![162, -392, -11, 104, 532], ![-58, 1458, -462, -1763, 156], ![-500, 1432, -28, -620, -1607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![6987065, 21492982, 20969860, 1487230, 6063962]] ![![3, 14, 8, -14, -26]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-401020397, -1233584069, -1203560283, -85359140, -348039732]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-401020397, -1233584069, -1203560283, -85359140, -348039732]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![17, 4, 1, 0, 0], ![15, 10, 0, 1, 0], ![7, 6, 0, 0, 1]] where
  M :=![![![-401020397, -1233584069, -1203560283, -85359140, -348039732], ![-696079464, -2141219057, -2089104620, -148163894, -604117152], ![-1208234304, -3716665224, -3626206525, -257178540, -1048608834], ![-444491682, -1367306625, -1334028195, -94612213, -385767810], ![-553506328, -1702647994, -1661207800, -117816510, -480380023]]]
  hmulB := by decide  
  f := ![![![-2215, -5063, 2299, 7974, -3450]], ![![-6900, -19465, 686, 9350, 20472]], ![![-1057, -2977, 112, 1426, 3120]], ![![-3225, -7676, 2818, 10371, -2490]], ![![-7755, -18721, 6309, 23828, -3745]]]
  g := ![![![1033746506, 283586385, -1203560283, -85359140, -348039732], ![1794346850, 492240925, -2089104620, -148163894, -604117152], ![3114574633, 854417360, -3626206525, -257178540, -1048608834], ![1145806326, 314327615, -1334028195, -94612213, -385767810], ![1426823221, 391418628, -1661207800, -117816510, -480380023]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [8, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 22], [0, 1]]
 g := ![![[12, 3], [15, 2], [0, 16], [1]], ![[0, 20], [7, 21], [5, 7], [1]]]
 h' := ![![[19, 22], [18, 16], [0, 5], [15, 19], [0, 1]], ![[0, 1], [0, 7], [3, 18], [8, 4], [19, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [8, 4, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1659, 2878, -3074, -9569, 10159]
  a := ![3, 0, 3, -7, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5493, 2170, -3074, -9569, 10159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2215, 5063, -2299, -7974, 3450]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![2215, 5063, -2299, -7974, 3450]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![1, 7, 10, 1, 0], ![17, 12, 7, 0, 1]] where
  M :=![![![2215, 5063, -2299, -7974, 3450], ![6900, 19465, -686, -9350, -20472], ![-40944, -95460, 39251, 140160, -48522], ![-28050, -94047, -23469, -25423, 210240], ![121460, 278352, -124898, -436126, 184817]]]
  hmulB := by decide  
  f := ![![![401020397, 1233584069, 1203560283, 85359140, 348039732]], ![![696079464, 2141219057, 2089104620, 148163894, 604117152]], ![![1208234304, 3716665224, 3626206525, 257178540, 1048608834]], ![![773930929, 2380698971, 2322755916, 164734957, 671683302]], ![![1051367251, 3234124453, 3155410162, 223788626, 912466223]]]
  g := ![![![-2107, 847, 2317, -7974, 3450], ![15838, 14373, 10266, -9350, -20472], ![27990, -21492, -44465, 140160, -48522], ![-155509, -106042, -53953, -25423, 210240], ![-112361, 48410, 127941, -436126, 184817]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 3 2 4 [11, 10, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 16, 11], [18, 6, 12], [0, 1]]
 g := ![![[22, 11, 8], [18, 5, 3], [3, 6, 1], []], ![[22, 22, 19, 15], [19, 16, 2, 5], [16, 11, 21, 5], [20, 6]], ![[15, 11, 3, 6], [22, 9, 12, 12], [20, 15, 8, 13], [19, 6]]]
 h' := ![![[11, 16, 11], [9, 3, 13], [13, 19, 16], [0, 0, 1], [0, 1]], ![[18, 6, 12], [20, 16, 19], [18, 1, 6], [16, 17, 6], [11, 16, 11]], ![[0, 1], [17, 4, 14], [10, 3, 1], [0, 6, 16], [18, 6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 19], []]
 b := ![[], [2, 7, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 3
  hpos := by decide
  P := [11, 10, 17, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![901731, 1961716, -1110068, -3681310, 2264750]
  a := ![1, 1, 1, -5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1474683, 24082, 863034, -3681310, 2264750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-401020397, -1233584069, -1203560283, -85359140, -348039732]] ![![2215, 5063, -2299, -7974, 3450]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB434I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB434I0 : PrimesBelowBoundCertificateInterval O 1 23 434 where
  m := 9
  g := ![5, 5, 5, 1, 3, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB434I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![121, 121, 11]
    · exact ![2197, 169]
    · exact ![1419857]
    · exact ![130321, 19]
    · exact ![529, 12167]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N0, I11N1, I11N2, I13N1, I19N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N0, I11N1, I11N2], [I13N1], [], [I19N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
