
import IdealArithmetic.Examples.NF5_1_24300000_2.RI5_1_24300000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -6, 3, 2, 6]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-10, -6, 3, 2, 6]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-10, -6, 3, 2, 6], ![30, -17, 4, -2, 18], ![66, -4, -3, -8, 6], ![-15, 30, -9, -1, -30], ![-45, 18, -3, 4, -19]]]
  hmulB := by decide  
  f := ![![![-5, 6, -3, 2, 0]], ![![3, -3, 5, -4, 6]], ![![12, -8, -5, 8, -18]], ![![-28, 30, -9, 3, 12]], ![![-1, 0, 6, -6, 11]]]
  g := ![![![-9, -6, 3, 2, 6], ![7, -17, 4, -2, 18], ![34, -4, -3, -8, 6], ![8, 30, -9, -1, -30], ![-15, 18, -3, 4, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55420, 13159, 22835, 5682, 27083]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![55420, 13159, 22835, 5682, 27083]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![55420, 13159, 22835, 5682, 27083], ![125378, 29771, 51606, 12905, 61175], ![283415, 67539, 116756, 29132, 138605], ![258219, 61161, 106401, 26435, 126111], ![-2750, -722, -1180, -254, -1467]]]
  hmulB := by decide  
  f := ![![![-81033, 15935, 487, 8933, -17548]], ![![-62213, -10291, 8370, 9261, 9251]], ![![45967, -36858, 9599, -2100, 38018]], ![![54066, 14941, -9403, -8688, -14090]], ![![689, 28899, -10311, -3173, -29141]]]
  g := ![![![6872, 13159, 22835, 5682, 27083], ![15548, 29771, 51606, 12905, 61175], ![34994, 67539, 116756, 29132, 138605], ![32111, 61161, 106401, 26435, 126111], ![-297, -722, -1180, -254, -1467]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, -1, 0, -1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-2, 0, -1, 0, -1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-2, 0, -1, 0, -1], ![-4, -1, -1, -1, -1], ![-7, -4, -4, 0, -7], ![-12, 2, -5, 0, -3], ![0, 0, 1, -1, 2]]]
  hmulB := by decide  
  f := ![![![9, -2, 0, -1, 2]], ![![7, 1, -1, -1, -1]], ![![-5, 4, -1, 0, -4]], ![![-6, -2, 1, 1, 1]], ![![4, -4, 1, 0, 4]]]
  g := ![![![0, 0, -1, 0, -1], ![0, -1, -1, -1, -1], ![4, -4, -4, 0, -7], ![-3, 2, -5, 0, -3], ![-1, 0, 1, -1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-10, -6, 3, 2, 6]] ![![55420, 13159, 22835, 5682, 27083]]
  ![![43715, 10391, 18004, 4492, 21355]] where
 M := ![![![43715, 10391, 18004, 4492, 21355]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![43715, 10391, 18004, 4492, 21355]] ![![55420, 13159, 22835, 5682, 27083]]
  ![![9929285256, 2359885204, 4089299387, 1020298863, 4850210017]] where
 M := ![![![9929285256, 2359885204, 4089299387, 1020298863, 4850210017]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![9929285256, 2359885204, 4089299387, 1020298863, 4850210017]] ![![-2, 0, -1, 0, -1]]
  ![![-70166793393, -16676485026, -28897652306, -7210095221, -34274742724]] where
 M := ![![![-70166793393, -16676485026, -28897652306, -7210095221, -34274742724]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-70166793393, -16676485026, -28897652306, -7210095221, -34274742724]] ![![-2, 0, -1, 0, -1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![495844235684, 117846903808, 204209621024, 50951227750, 242207644776]]]
 hmul := by decide  
 g := ![![![![247922117842, 58923451904, 102104810512, 25475613875, 121103822388]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4312583, -1024968, -1776104, -443146, -2106590]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-4312583, -1024968, -1776104, -443146, -2106590]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-4312583, -1024968, -1776104, -443146, -2106590], ![-9755798, -2318653, -4017850, -1002472, -4765466], ![-22069280, -5245188, -9089063, -2267762, -10780298], ![-20084340, -4773428, -8271580, -2063797, -9810702], ![218928, 52032, 90164, 22496, 106941]]]
  hmulB := by decide  
  f := ![![![3, -1600, 568, 170, 1614]], ![![2322, -829, 118, -216, 878]], ![![2864, 468, -383, -426, -418]], ![![-2636, 1860, -460, 147, -1926]], ![![-2991, 176, 164, 374, -233]]]
  g := ![![![-735331, -1024968, -1776104, -443146, -2106590], ![-1663444, -2318653, -4017850, -1002472, -4765466], ![-3762994, -5245188, -9089063, -2267762, -10780298], ![-3424546, -4773428, -8271580, -2063797, -9810702], ![37329, 52032, 90164, 22496, 106941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-318, -87, 55, 51, 82]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-318, -87, 55, 51, 82]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-318, -87, 55, 51, 82], ![481, -376, 97, -23, 388], ![1483, -221, -34, -171, 250], ![3, 577, -205, -62, -582], ![-834, 426, -88, 64, -445]]]
  hmulB := by decide  
  f := ![![![822, 199, 341, 83, 408]], ![![1175, 276, 485, 119, 574]], ![![1947, 477, 800, 205, 956]], ![![1279, 305, 535, 124, 640]], ![![268, 55, 111, 25, 127]]]
  g := ![![![-112, -87, 55, 51, 82], ![217, -376, 97, -23, 388], ![581, -221, -34, -171, 250], ![-53, 577, -205, -62, -582], ![-355, 426, -88, 64, -445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-4312583, -1024968, -1776104, -443146, -2106590]] ![![-4312583, -1024968, -1776104, -443146, -2106590]]
  ![![76234192779593, 18118519521608, 31396463755904, 7833560322984, 37238517283352]] where
 M := ![![![76234192779593, 18118519521608, 31396463755904, 7833560322984, 37238517283352]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![76234192779593, 18118519521608, 31396463755904, 7833560322984, 37238517283352]] ![![-318, -87, 55, 51, 82]]
  ![![67602641890, 16067065737, 27841626159, 6946612195, 33022218202]] where
 M := ![![![67602641890, 16067065737, 27841626159, 6946612195, 33022218202]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![67602641890, 16067065737, 27841626159, 6946612195, 33022218202]] ![![-318, -87, 55, 51, 82]]
  ![![59948391, 14247886, 24689282, 6160088, 29283306]] where
 M := ![![![59948391, 14247886, 24689282, 6160088, 29283306]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![59948391, 14247886, 24689282, 6160088, 29283306]] ![![-318, -87, 55, 51, 82]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![53094, 12657, 21891, 5469, 25944]]]
 hmul := by decide  
 g := ![![![![17698, 4219, 7297, 1823, 8648]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7464, 1774, 3074, 767, 3646]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![7464, 1774, 3074, 767, 3646]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![7464, 1774, 3074, 767, 3646], ![16885, 4013, 6954, 1735, 8248], ![38197, 9078, 15731, 3925, 18658], ![34761, 8262, 14316, 3572, 16980], ![-379, -90, -156, -39, -185]]]
  hmulB := by decide  
  f := ![![![-58, 2, 4, 7, -8]], ![![-37, -5, 4, 6, 2]], ![![21, -12, 5, -4, 16]], ![![5, 2, -2, 0, -14]], ![![-55, 14, -2, 7, -19]]]
  g := ![![![-3410, 1774, 3074, 767, 3646], ![-7714, 4013, 6954, 1735, 8248], ![-17450, 9078, 15731, 3925, 18658], ![-15881, 8262, 14316, 3572, 16980], ![173, -90, -156, -39, -185]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![7464, 1774, 3074, 767, 3646]] ![![7464, 1774, 3074, 767, 3646]]
  ![![228362717, 54274784, 94049422, 23465758, 111549538]] where
 M := ![![![228362717, 54274784, 94049422, 23465758, 111549538]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![228362717, 54274784, 94049422, 23465758, 111549538]] ![![7464, 1774, 3074, 767, 3646]]
  ![![6986750758598, 1660535455242, 2877439361076, 717934191123, 3412854906600]] where
 M := ![![![6986750758598, 1660535455242, 2877439361076, 717934191123, 3412854906600]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![6986750758598, 1660535455242, 2877439361076, 717934191123, 3412854906600]] ![![7464, 1774, 3074, 767, 3646]]
  ![![213759438506981817, 50804034492951152, 88035174491456944, 21965175928246792, 104416197707187872]] where
 M := ![![![213759438506981817, 50804034492951152, 88035174491456944, 21965175928246792, 104416197707187872]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![213759438506981817, 50804034492951152, 88035174491456944, 21965175928246792, 104416197707187872]] ![![7464, 1774, 3074, 767, 3646]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![6539963872990535906800, 1554347974090572940990, 2693433631506013368770, 672023925764211021575, 3194610565641721239470]]]
 hmul := by decide  
 g := ![![![![1307992774598107181360, 310869594818114588198, 538686726301202673754, 134404785152842204315, 638922113128344247894]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23528934, 5592102, 9690210, 2417751, 11493302]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![23528934, 5592102, 9690210, 2417751, 11493302]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![6, 5, 2, 1, 0], ![1, 6, 6, 0, 1]] where
  M :=![![![23528934, 5592102, 9690210, 2417751, 11493302], ![53226461, 12650291, 21920906, 5469367, 25999808], ![120407333, 28617118, 49588833, 12372637, 58816010], ![109577745, 26043246, 45128748, 11259826, 53526012], ![-1194443, -283882, -491924, -122735, -583459]]]
  hmulB := by decide  
  f := ![![![-7984, -3050, 1688, 1373, 2932]], ![![15847, -10787, 2628, -929, 11170]], ![![41893, -4794, -1475, -4985, 5596]], ![![15844, -9187, 2060, -1099, 9556]], ![![44665, -12098, 908, -4570, 13015]]]
  g := ![![![-352982, -10779495, -9157872, 2417751, 11493302], ![-798507, -24385056, -20716668, 5469367, 25999808], ![-1806357, -55163161, -46864643, 12372637, 58816010], ![-1643889, -50201708, -42649568, 11259826, 53526012], ![17918, 547221, 464900, -122735, -583459]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 5], [6, 6, 2], [0, 1]]
 g := ![![[1], [1]], ![[6, 5, 0, 6], [6, 6, 0, 6]], ![[4, 6, 2, 1], [3, 0, 2, 1]]]
 h' := ![![[1, 0, 5], [1, 6], [0, 1]], ![[6, 6, 2], [0, 0, 2], [1, 0, 5]], ![[0, 1], [2, 1, 5], [6, 6, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 1, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85530, -101098, -23252, -34134, -68648]
  a := ![-13, -7, -11, 0, -26]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26846, 68780, 65272, -34134, -68648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-648, -656, 282, 155, 650]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-648, -656, 282, 155, 650]] 
 ![![7, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-648, -656, 282, 155, 650], ![3065, -1511, 304, -241, 1580], ![5597, -32, -413, -731, 134], ![-2361, 2848, -832, 6, -2916], ![-4387, 1506, -202, 415, -1599]]]
  hmulB := by decide  
  f := ![![![-238, 48, -44, -51, 40]], ![![1, -59, -2, -11, -38]], ![![-185, 64, -119, 45, -104]], ![![-141, 4, 26, -84, 102]], ![![-55, -54, 12, -47, 11]]]
  g := ![![![-464, -656, 282, 155, 650], ![-465, -1511, 304, -241, 1580], ![723, -32, -413, -731, 134], ![1329, 2848, -832, 6, -2916], ![287, 1506, -202, 415, -1599]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![132, -59, 11, -11, 62]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![132, -59, 11, -11, 62]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![132, -59, 11, -11, 62], ![215, 8, -19, -29, -4], ![-103, 175, -54, -5, -178], ![-471, 93, 3, 52, -102], ![-188, -50, 32, 30, 47]]]
  hmulB := by decide  
  f := ![![![-16, 15, 21, -23, 52]], ![![13, -11, 12, -8, 10]], ![![-55, 60, -11, 0, 36]], ![![1, -6, 54, -51, 92]], ![![20, -20, 26, -20, 27]]]
  g := ![![![-9, -59, 11, -11, 62], ![65, 8, -19, -29, -4], ![105, 175, -54, -5, -178], ![-59, 93, 3, 52, -102], ![-90, -50, 32, 30, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![23528934, 5592102, 9690210, 2417751, 11493302]] ![![-648, -656, 282, 155, 650]]
  ![![-277217, -65886, -114170, -28486, -135414]] where
 M := ![![![-277217, -65886, -114170, -28486, -135414]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-277217, -65886, -114170, -28486, -135414]] ![![132, -59, 11, -11, 62]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-123886, -29533, -51079, -12761, -60536]]]
 hmul := by decide  
 g := ![![![![-17698, -4219, -7297, -1823, -8648]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7858288, -1867675, -3236375, -807491, -3838580]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-7858288, -1867675, -3236375, -807491, -3838580]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![4, 6, 8, 1, 0], ![7, 0, 7, 0, 1]] where
  M :=![![![-7858288, -1867675, -3236375, -807491, -3838580], ![-17776793, -4224994, -7321237, -1826679, -8683526], ![-40214141, -9557657, -16561878, -4132269, -19643600], ![-36597207, -8698047, -15072279, -3760604, -17876844], ![398924, 94814, 164290, 40996, 194859]]]
  hmulB := by decide  
  f := ![![![2544, 4699, -1861, -835, -4694]], ![![-21281, 9236, -1665, 1807, -9704]], ![![-33395, -1731, 3146, 4567, 1138]], ![![-33173, 3797, 1167, 3948, -4434]], ![![-16983, 1094, 899, 2112, -1413]]]
  g := ![![![2021976, 270661, 2735783, -807491, -3838580], ![4574055, 612280, 6188807, -1826679, -8683526], ![10347285, 1385087, 14000134, -4132269, -19643600], ![9416647, 1260507, 12740951, -3760604, -17876844], ![-102643, -13742, -138881, 40996, 194859]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [5, 5, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 4], [6, 5, 7], [0, 1]]
 g := ![![[2, 8, 5], [0, 7, 1], []], ![[4, 1, 2, 4], [7, 10, 9, 1], [9, 5]], ![[10, 6, 1, 10], [10, 8, 6, 10], [6, 5]]]
 h' := ![![[1, 5, 4], [0, 9, 4], [0, 0, 1], [0, 1]], ![[6, 5, 7], [9, 3, 1], [0, 6, 5], [1, 5, 4]], ![[0, 1], [1, 10, 6], [6, 5, 5], [6, 5, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 3], []]
 b := ![[], [2, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [5, 5, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25373941, -36582172, 8047830, -5388196, -15728534]
  a := ![19, -56, 15, -67, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14275133, -386636, 14659376, -5388196, -15728534]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2544, 4699, -1861, -835, -4694]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![2544, 4699, -1861, -835, -4694]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 6, 1, 0, 0], ![2, 6, 0, 1, 0], ![6, 10, 0, 0, 1]] where
  M :=![![![2544, 4699, -1861, -835, -4694], ![-21281, 9236, -1665, 1807, -9704], ![-33395, -1731, 3146, 4567, 1138], ![19767, -18597, 5103, -610, 19122], ![29144, -8742, 894, -2892, 9349]]]
  hmulB := by decide  
  f := ![![![-7858288, -1867675, -3236375, -807491, -3838580]], ![![-17776793, -4224994, -7321237, -1826679, -8683526]], ![![-15495433, -3682786, -6381675, -1592256, -7569136]], ![![-14452231, -3434851, -5952041, -1485060, -7059560]], ![![-20410794, -4851016, -8406030, -2097340, -9970171]]]
  g := ![![![3451, 6165, -1861, -835, -4694], ![3484, 9584, -1665, 1807, -9704], ![-5345, -5399, 3146, 4567, 1138], ![-9914, -21525, 5103, -610, 19122], ![-2168, -8204, 894, -2892, 9349]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[4, 4], [5, 4], [1]], ![[7, 7], [8, 7], [1]]]
 h' := ![![[9, 10], [3, 2], [5, 9], [0, 1]], ![[0, 1], [10, 9], [9, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [10, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [6, 2, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![212, 158, 124, -7, 203]
  a := ![-2, -4, -2, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-124, -234, 124, -7, 203]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-7858288, -1867675, -3236375, -807491, -3838580]] ![![2544, 4699, -1861, -835, -4694]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, 21, -5, 2, -22]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-33, 21, -5, 2, -22]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![12, 1, 5, 1, 0], ![2, 8, 6, 0, 1]] where
  M :=![![![-33, 21, -5, 2, -22], ![-82, 8, 3, 10, -10], ![-10, -49, 18, 6, 50], ![150, -47, 5, -15, 48], ![83, 4, -8, -11, -3]]]
  hmulB := by decide  
  f := ![![![-7, 1, -3, 0, -2]], ![![-8, -6, -1, -4, -2]], ![![-20, -9, -16, 4, -26]], ![![-18, -2, -10, 1, -12]], ![![-15, -8, -8, -1, -13]]]
  g := ![![![-1, 15, 9, 2, -22], ![-14, 6, 1, 10, -10], ![-14, -35, -24, 6, 50], ![18, -32, -16, -15, 48], ![17, 3, 5, -11, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [4, 1, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 9, 12], [0, 3, 1], [0, 1]]
 g := ![![[9, 1, 12], [8, 9], [1]], ![[0, 9, 8, 12], [3, 9], [12, 8, 11, 12]], ![[0, 7, 11, 3], [], [2, 10, 12, 1]]]
 h' := ![![[3, 9, 12], [10, 3, 5], [9, 12, 3], [0, 1]], ![[0, 3, 1], [0, 1, 12], [5, 4, 10], [3, 9, 12]], ![[0, 1], [12, 9, 9], [5, 10], [0, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 10], []]
 b := ![[], [6, 10, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [4, 1, 10, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3858276, 305874, 1389628, 411468, 1233192]
  a := ![23, 27, 19, 12, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-272748, -767010, -620528, 411468, 1233192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-184, -44, -76, -19, -90]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-184, -44, -76, -19, -90]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-184, -44, -76, -19, -90], ![-417, -99, -172, -43, -204], ![-945, -224, -389, -97, -462], ![-861, -204, -354, -88, -420], ![9, 2, 4, 1, 5]]]
  hmulB := by decide  
  f := ![![![14, -4, -2, 1, -12]], ![![3, 1, -2, 1, -6]], ![![3, -4, 3, -2, 0]], ![![5, -4, -2, 3, -6]], ![![1, 2, -2, 1, -1]]]
  g := ![![![39, -44, -76, -19, -90], ![88, -99, -172, -43, -204], ![199, -224, -389, -97, -462], ![181, -204, -354, -88, -420], ![-2, 2, 4, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 9, -7, 5, -4]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-8, 9, -7, 5, -4]] 
 ![![13, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-8, 9, -7, 5, -4], ![-1, -2, 15, -15, 26], ![59, -53, -6, 19, -64], ![-99, 101, -47, 24, 12], ![-12, 6, 22, -24, 47]]]
  hmulB := by decide  
  f := ![![![120, 41, 45, 11, 46]], ![![109, 38, 43, 11, 44]], ![![79, 23, 34, 9, 38]], ![![57, 10, 22, 5, 28]], ![![88, 27, 31, 7, 33]]]
  g := ![![![-3, 9, -7, 5, -4], ![-20, -2, 15, -15, 26], ![90, -53, -6, 19, -64], ![-81, 101, -47, 24, 12], ![-43, 6, 22, -24, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-33, 21, -5, 2, -22]] ![![-184, -44, -76, -19, -90]]
  ![![120, 41, 45, 11, 46]] where
 M := ![![![120, 41, 45, 11, 46]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![120, 41, 45, 11, 46]] ![![-8, 9, -7, 5, -4]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7723, 1834, 3182, 792, 3774]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![7723, 1834, 3182, 792, 3774]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![7, 16, 1, 0, 0], ![12, 12, 0, 1, 0], ![6, 15, 0, 0, 1]] where
  M :=![![![7723, 1834, 3182, 792, 3774], ![17472, 4149, 7192, 1798, 8526], ![39498, 9410, 16271, 4060, 19314], ![35982, 8526, 14826, 3685, 17574], ![-384, -100, -164, -36, -203]]]
  hmulB := by decide  
  f := ![![![2639, -434, -46, -300, 486]], ![![1044, 1321, -548, -278, -1314]], ![![1711, 1232, -567, -356, -1212]], ![![2262, 582, -378, -359, -546]], ![![1878, 895, -460, -342, -869]]]
  g := ![![![-2747, -6776, 3182, 792, 3774], ![-6212, -15317, 7192, 1798, 8526], ![-14059, -34668, 16271, 4060, 19314], ![-12792, -31560, 14826, 3685, 17574], ![142, 353, -164, -36, -203]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [7, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 16], [0, 1]]
 g := ![![[8, 15], [16], [8], [1]], ![[1, 2], [16], [8], [1]]]
 h' := ![![[12, 16], [5, 10], [10, 13], [10, 12], [0, 1]], ![[0, 1], [6, 7], [13, 4], [1, 5], [12, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [13, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [7, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8325, -4067, -1477, 4604, -8262]
  a := ![-33, -9, -27, 15, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![764, 5191, -1477, 4604, -8262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 41, 25, 2, 54]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![37, 41, 25, 2, 54]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![11, 0, 1, 0, 0], ![0, 6, 0, 1, 0], ![0, 4, 0, 0, 1]] where
  M :=![![![37, 41, 25, 2, 54], ![222, -44, 99, -6, 66], ![246, 183, 10, 138, 30], ![156, 189, 195, -71, 396], ![117, -128, 74, -47, 13]]]
  hmulB := by decide  
  f := ![![![2003, 161, -209, -280, -126]], ![![-1344, 1766, -525, -12, -1806]], ![![869, 206, -139, -136, -192]], ![![-588, 489, -129, 25, -504]], ![![-135, 288, -92, -13, -293]]]
  g := ![![![-14, -11, 25, 2, 54], ![-51, -16, 99, -6, 66], ![8, -45, 10, 138, 30], ![-117, -57, 195, -71, 396], ![-41, 6, 74, -47, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [12, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 16], [0, 1]]
 g := ![![[14, 13], [2], [4], [1]], ![[6, 4], [2], [4], [1]]]
 h' := ![![[2, 16], [12, 8], [11, 11], [5, 2], [0, 1]], ![[0, 1], [11, 9], [16, 6], [9, 15], [2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [10, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [12, 15, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-650, 3060, -4612, 3846, -5412]
  a := ![14, -4, 12, -22, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2946, 96, -4612, 3846, -5412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-503882, -119761, -207521, -51777, -246138]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-503882, -119761, -207521, -51777, -246138]] 
 ![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-503882, -119761, -207521, -51777, -246138], ![-1139883, -270904, -469453, -117127, -556800], ![-2578581, -612863, -1061958, -264979, -1259562], ![-2346651, -557745, -966465, -241124, -1146318], ![25566, 6094, 10526, 2634, 12493]]]
  hmulB := by decide  
  f := ![![![-30238, -30949, 13279, 7269, 30672]], ![![6721, -5999, 1620, -242, 6174]], ![![-12989, -29199, 11350, 4819, 29220]], ![![-6579, 7887, -2301, 22, -8076]], ![![-33498, -17686, 8818, 6282, 17233]]]
  g := ![![![346463, -119761, -207521, -51777, -246138], ![783757, -270904, -469453, -117127, -556800], ![1772962, -612863, -1061958, -264979, -1259562], ![1613550, -557745, -966465, -241124, -1146318], ![-17580, 6094, 10526, 2634, 12493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![7723, 1834, 3182, 792, 3774]] ![![37, 41, 25, 2, 54]]
  ![![2040781, 484869, 840177, 209948, 996240]] where
 M := ![![![2040781, 484869, 840177, 209948, 996240]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![2040781, 484869, 840177, 209948, 996240]] ![![-503882, -119761, -207521, -51777, -246138]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-4214676003314, -1001698682368, -1735781778704, -433085435875, -2058764980596]]]
 hmul := by decide  
 g := ![![![![-247922117842, -58923451904, -102104810512, -25475613875, -121103822388]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [8, 14, 4, 2, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 14, 8, 17, 9], [0, 6, 2, 14, 15], [15, 17, 9, 5, 6], [1, 0, 0, 2, 8], [0, 1]]
 g := ![![[17, 12, 6, 12, 7], [16, 13, 15, 13, 1], [], []], ![[0, 4, 6, 10, 2, 3, 9, 17], [13, 8, 15, 17, 1, 9, 12, 7], [6, 2, 5, 5], [16, 2, 10, 5]], ![[10, 7, 13, 0, 11, 17, 11, 18], [18, 17, 8, 12, 1, 3, 14, 18], [10, 10, 14, 5], [2, 9, 1, 16]], ![[12, 6, 4, 5, 6, 18, 5, 6], [7, 10, 18, 18, 3, 15, 16, 6], [14, 16, 10, 16], [9, 9, 15, 17]], ![[13, 16, 15, 11, 9, 12, 4, 13], [1, 2, 14, 8, 11, 2, 4, 8], [7, 9, 14, 16], [15, 12, 9, 7]]]
 h' := ![![[16, 14, 8, 17, 9], [5, 14, 14, 1, 8], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 6, 2, 14, 15], [0, 3, 11, 7, 2], [15, 5, 16, 5, 10], [14, 18, 14, 16, 10], [16, 14, 8, 17, 9]], ![[15, 17, 9, 5, 6], [8, 9, 9, 2, 10], [5, 16, 9, 6, 10], [3, 14, 8, 13, 9], [0, 6, 2, 14, 15]], ![[1, 0, 0, 2, 8], [3, 14, 2, 3, 1], [3, 15, 11, 4, 18], [1, 8, 11, 18, 4], [15, 17, 9, 5, 6]], ![[0, 1], [3, 17, 2, 6, 17], [7, 2, 2, 4, 18], [14, 17, 4, 10, 15], [1, 0, 0, 2, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 10, 0, 16], [], [], []]
 b := ![[], [5, 7, 17, 7, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [8, 14, 4, 2, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124197219250, 30213799886, 53489221249, 10761819887, 65069013537]
  a := ![29, 19, 20, 10, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6536695750, 1590199994, 2815222171, 566411573, 3424684923]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81883, 19461, 33723, 8414, 39998]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![81883, 19461, 33723, 8414, 39998]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![10, 9, 5, 1, 0], ![20, 16, 2, 0, 1]] where
  M :=![![![81883, 19461, 33723, 8414, 39998], ![185234, 44024, 76287, 19034, 90482], ![419030, 99591, 172574, 43058, 204686], ![381342, 90633, 157053, 39185, 186276], ![-4157, -988, -1712, -427, -2031]]]
  hmulB := by decide  
  f := ![![![-57, 19, -1, 4, -10]], ![![-28, -34, 17, 4, 14]], ![![68, -35, -12, 16, 38]], ![![-16, -12, 4, 5, 12]], ![![-61, -10, 10, 7, 3]]]
  g := ![![![-34879, -30271, -3841, 8414, 39998], ![-78902, -68478, -8689, 19034, 90482], ![-178490, -154909, -19656, 43058, 204686], ![-162436, -140976, -17888, 39185, 186276], ![1771, 1537, 195, -427, -2031]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [1, 18, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 6, 14], [16, 16, 9], [0, 1]]
 g := ![![[16, 21, 2], [19, 19, 1], [5, 0, 1], []], ![[14, 3, 5, 14], [9, 16, 17, 15], [7, 7, 22, 19], [7, 12]], ![[4, 0, 3, 6], [2, 2, 13, 8], [18, 1, 14, 2], [12, 12]]]
 h' := ![![[7, 6, 14], [4, 9, 5], [18, 2, 22], [0, 0, 1], [0, 1]], ![[16, 16, 9], [1, 14, 22], [13, 20, 12], [19, 15, 16], [7, 6, 14]], ![[0, 1], [11, 0, 19], [13, 1, 12], [14, 8, 6], [16, 16, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 19], []]
 b := ![[], [13, 19, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [1, 18, 0, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26274, -29673, 20217, -14412, 9327]
  a := ![3, -3, 3, -6, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-702, -2139, 3201, -14412, 9327]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, -19, 1, -4, 10]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![57, -19, 1, -4, 10]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![14, 13, 1, 0, 0], ![1, 15, 0, 1, 0], ![7, 12, 0, 0, 1]] where
  M :=![![![57, -19, 1, -4, 10], ![28, 34, -17, -4, -14], ![-68, 35, 12, -16, -38], ![-114, -15, -9, 41, -60], ![-49, -4, -2, 15, 31]]]
  hmulB := by decide  
  f := ![![![-81883, -19461, -33723, -8414, -39998]], ![![-185234, -44024, -76287, -19034, -90482]], ![![-172758, -41059, -71149, -17752, -84388]], ![![-140945, -33498, -58047, -14483, -68848]], ![![-121384, -28849, -49991, -12473, -59293]]]
  g := ![![![-1, -4, 1, -4, 10], ![16, 21, -17, -4, -14], ![2, 25, 12, -16, -38], ![17, 9, -9, 41, -60], ![-11, -25, -2, 15, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [11, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 22], [0, 1]]
 g := ![![[16, 12], [9, 6], [14, 18], [1]], ![[20, 11], [11, 17], [20, 5], [1]]]
 h' := ![![[8, 22], [16, 9], [7, 12], [12, 8], [0, 1]], ![[0, 1], [19, 14], [11, 11], [7, 15], [8, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [5, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [11, 15, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4509, -363, 1727, 522, 858]
  a := ![19, 9, 16, -1, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1139, -1780, 1727, 522, 858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![81883, 19461, 33723, 8414, 39998]] ![![57, -19, 1, -4, 10]]
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


lemma PB307I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB307I0 : PrimesBelowBoundCertificateInterval O 1 23 307 where
  m := 9
  g := ![5, 5, 5, 3, 2, 3, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB307I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
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
    · exact ![343, 7, 7]
    · exact ![1331, 121]
    · exact ![2197, 13, 13]
    · exact ![289, 289, 17]
    · exact ![2476099]
    · exact ![12167, 529]
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
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I7N2, I11N1, I13N1, I13N2, I17N0, I17N1, I17N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1, I7N2], [I11N1], [I13N1, I13N2], [I17N0, I17N1, I17N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
