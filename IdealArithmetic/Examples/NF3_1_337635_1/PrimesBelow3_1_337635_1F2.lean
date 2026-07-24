
import IdealArithmetic.Examples.NF3_1_337635_1.RI3_1_337635_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -7, -1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-23, -7, -1]] 
 ![![83, 0, 0], ![38, 1, 0], ![6, 0, 1]] where
  M :=![![![-23, -7, -1], ![-268, -88, -13], ![-1608, -511, -75]]]
  hmulB := by decide  
  f := ![![![43, 14, -3]], ![![10, 5, -1]], ![![58, 7, -2]]]
  g := ![![![3, -7, -1], ![38, -88, -13], ![220, -511, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54603, -1908, 1072]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-54603, -1908, 1072]] 
 ![![83, 0, 0], ![50, 1, 0], ![53, 0, 1]] where
  M :=![![![-54603, -1908, 1072], ![287296, 5665, -4888], ![-798640, 1896, 10553]]]
  hmulB := by decide  
  f := ![![![-69050393, -22167636, -3253424]], ![![-52101654, -16726487, -2454856]], ![![-105164815, -33761652, -4955015]]]
  g := ![![![-193, -1908, 1072], ![3170, 5665, -4888], ![-17503, 1896, 10553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-373647, -119954, -17605]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-373647, -119954, -17605]] 
 ![![83, 0, 0], ![78, 1, 0], ![73, 0, 1]] where
  M :=![![![-373647, -119954, -17605], ![-4718140, -1514691, -222303], ![-27429532, -8805857, -1292388]]]
  hmulB := by decide  
  f := ![![![-43437, -2333, 993]], ![![-37614, -2050, 865]], ![![-48943, -2426, 1084]]]
  g := ![![![123710, -119954, -17605], ![1562119, -1514691, -222303], ![9081586, -8805857, -1292388]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-23, -7, -1]] ![![-54603, -1908, 1072]]
  ![![43437, 2333, -993]] where
 M := ![![![43437, 2333, -993]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![43437, 2333, -993]] ![![-373647, -119954, -17605]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68775106972212942025315450441799, 22079259377843733172367844473576, 3240453441128620174987776795373]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![68775106972212942025315450441799, 22079259377843733172367844473576, 3240453441128620174987776795373]] 
 ![![89, 0, 0], ![0, 89, 0], ![66, 74, 1]] where
  M :=![![![68775106972212942025315450441799, 22079259377843733172367844473576, 3240453441128620174987776795373], ![868441522222470206896724181159964, 278800665935516645346974349047009, 40918065314558846169747912151779], ![5048799991039650283297858137758404, 1620844655233441642371051542981573, 237882600620957799177226436895230]]]
  hmulB := by decide  
  f := ![![![50451063589906727, 4350686340620441, -1435607268357277]], ![![-384742747919750236, -28463471634194898, 10136979949598159]], ![![-265061420920467922, -19298320874955077, 6930179606459443]]]
  g := ![![![-1630278878003101005886267618571, -2446228036692968087378962229034, 3240453441128620174987776795373], ![-20585963916161951014681326077050, -30889170419571213159712035395333, 40918065314558846169747912151779], ![-119679232021837802948304344913784, -179578289783341971873524772890623, 237882600620957799177226436895230]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [31, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 88], [0, 1]]
 g := ![![[17, 36], [4], [21], [56, 20], [87, 49], [1]], ![[2, 53], [4], [21], [18, 69], [74, 40], [1]]]
 h' := ![![[7, 88], [62, 6], [39, 2], [44, 56], [62, 51], [58, 7], [0, 1]], ![[0, 1], [15, 83], [53, 87], [80, 33], [63, 38], [18, 82], [7, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [45, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [31, 82, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![835, 1481, 281]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-199, -217, 281]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383689074323166839699719851076435, 123177861371392892907918171808945, 18078148271238595698444301038101]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![383689074323166839699719851076435, 123177861371392892907918171808945, 18078148271238595698444301038101]] 
 ![![89, 0, 0], ![31, 1, 0], ![38, 0, 1]] where
  M :=![![![383689074323166839699719851076435, 123177861371392892907918171808945, 18078148271238595698444301038101], ![4844943736691943647183072678211068, 1555399535426398283117407483095238, 228277574471547190117392042579789], ![28166723110841351652138997366586192, 9042521528020840336995905573919415, 1327121960954851093000015440515449]]]
  hmulB := by decide  
  f := ![![![-693606863916371573, 4394424269739610, 8692478576749567]], ![![-215418298009422863, -548556514980103, 3028800065640070]], ![![-309089206551694250, 14995224499479855, 1631113862456144]]]
  g := ![![![-46312295084236848056029515892682, 123177861371392892907918171808945, 18078148271238595698444301038101], ![-584797636982530296111432100177228, 1555399535426398283117407483095238, 228277574471547190117392042579789], ![-3399798637911112812682411934432615, 9042521528020840336995905573919415, 1327121960954851093000015440515449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![68775106972212942025315450441799, 22079259377843733172367844473576, 3240453441128620174987776795373]] ![![383689074323166839699719851076435, 123177861371392892907918171808945, 18078148271238595698444301038101]]
  ![![89, 0, 0]] where
 M := ![![![224633981393968908129667964353479920814890475952527064503095935349, 72115510373237813434833330201507203615312295643098522144499389938, 10584003283289799895591787257813820324028535270979464696982356640]]]
 hmul := by decide  
 g := ![![![![2523977319033358518310876003971684503538095235421652410147145341, 810286633407166443088014946084350602419239276888747439825835842, 118921385205503369613390868065323823865489160348083872999801760]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [56, 80, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 85, 53], [71, 11, 44], [0, 1]]
 g := ![![[38, 96, 1], [18, 24], [15, 70], [77, 72], [50, 12], [1]], ![[81, 84, 45, 24], [27, 4], [46, 79], [43, 93], [35, 4], [32, 22, 19, 79]], ![[18, 21, 46, 94], [74, 81], [4, 54], [69, 88], [21, 33], [22, 46, 90, 18]]]
 h' := ![![[6, 85, 53], [16, 58, 1], [65, 92, 86], [41, 47, 78], [45, 20, 84], [41, 17, 77], [0, 1]], ![[71, 11, 44], [28, 72, 78], [45, 51, 2], [14, 73, 51], [71, 58, 44], [73, 53, 2], [6, 85, 53]], ![[0, 1], [54, 64, 18], [67, 51, 9], [0, 74, 65], [88, 19, 66], [10, 27, 18], [71, 11, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 83], []]
 b := ![[], [56, 50, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [56, 80, 20, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1508835, 982513, 223682]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15555, 10129, 2306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77895, -3040, 1584]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-77895, -3040, 1584]] 
 ![![101, 0, 0], ![0, 101, 0], ![26, 95, 1]] where
  M :=![![![-77895, -3040, 1584], ![424512, 10937, -7664], ![-1239232, -10000, 18601]]]
  hmulB := by decide  
  f := ![![![1255437, 403040, 59152]], ![![15852736, 5089293, 746928]], ![![16146666, 5183655, 760777]]]
  g := ![![![-1179, -1520, 1584], ![6176, 7317, -7664], ![-17058, -17595, 18601]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [18, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 100], [0, 1]]
 g := ![![[31, 33], [54], [8, 49], [84], [56], [48, 1]], ![[100, 68], [54], [37, 52], [84], [56], [96, 100]]]
 h' := ![![[48, 100], [69, 29], [58, 85], [52, 94], [7, 65], [45, 64], [0, 1]], ![[0, 1], [47, 72], [98, 16], [19, 7], [97, 36], [87, 37], [48, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [25, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [18, 53, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![454, 105, 134]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -125, 134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1255437, -403040, -59152]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-1255437, -403040, -59152]] 
 ![![101, 0, 0], ![13, 1, 0], ![10, 0, 1]] where
  M :=![![![-1255437, -403040, -59152], ![-15852736, -5089293, -746928], ![-92161984, -29587280, -4342365]]]
  hmulB := by decide  
  f := ![![![77895, 3040, -1584]], ![![5823, 283, -128]], ![![19982, 400, -341]]]
  g := ![![![45303, -403040, -59152], ![572053, -5089293, -746928], ![3325706, -29587280, -4342365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-77895, -3040, 1584]] ![![-1255437, -403040, -59152]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-166828359982743, -9306005848120, 3873268939762]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-166828359982743, -9306005848120, 3873268939762]] 
 ![![103, 0, 0], ![0, 103, 0], ![7, 27, 1]] where
  M :=![![![-166828359982743, -9306005848120, 3873268939762], ![1038036075856216, 48515232675333, -22485280636002], ![-3532045643152376, -133055100515950, 71000513311335]]]
  hmulB := by decide  
  f := ![![![-4396360662280632586976385, -1411388388247237093342100, -207141837558837061511898]], ![![-55514012465768332485188664, -17821975628940419248008569, -2615634938935637125172302]], ![![-17984378027147578774169153, -5773626020981938079827351, -847363853438629552748269]]]
  g := ![![![-1882924685059, -1105672497298, 3873268939762], ![11606146022410, 6365221454829, -22485280636002], ![-39116982877007, -19903582135165, 71000513311335]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [19, 76, 1] where
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
 g := ![![[4, 38], [89, 52], [24, 9], [76], [18], [27, 1]], ![[0, 65], [51, 51], [61, 94], [76], [18], [54, 102]]]
 h' := ![![[27, 102], [60, 55], [59, 84], [15, 3], [74, 30], [2, 92], [0, 1]], ![[0, 1], [0, 48], [61, 19], [96, 100], [60, 73], [14, 11], [27, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [92, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [19, 76, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1244, 3633, 1073]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-85, -246, 1073]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4396360662280632586976385, -1411388388247237093342100, -207141837558837061511898]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-4396360662280632586976385, -1411388388247237093342100, -207141837558837061511898]] 
 ![![103, 0, 0], ![50, 1, 0], ![64, 0, 1]] where
  M :=![![![-4396360662280632586976385, -1411388388247237093342100, -207141837558837061511898], ![-55514012465768332485188664, -17821975628940419248008569, -2615634938935637125172302], ![-322738075584491208530494136, -103610419462017642872591090, -15206340690004782122836267]]]
  hmulB := by decide  
  f := ![![![-166828359982743, -9306005848120, 3873268939762]], ![![-70906620614378, -4046456890589, 1661923945166]], ![![-137952045456776, -7074169658210, 3096016752001]]]
  g := ![![![771166372367444602105729, -1411388388247237093342100, -207141837558837061511898], ![9737722379350809766274438, -17821975628940419248008569, -2615634938935637125172302], ![56611540792977640688937684, -103610419462017642872591090, -15206340690004782122836267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-166828359982743, -9306005848120, 3873268939762]] ![![-4396360662280632586976385, -1411388388247237093342100, -207141837558837061511898]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [19, 33, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 80, 52], [47, 26, 55], [0, 1]]
 g := ![![[66, 17, 44], [18, 104, 41], [71, 85], [102, 2, 101], [18, 44], [1]], ![[62, 88, 63, 30], [77, 34, 74, 13], [7, 42], [40, 38, 33, 53], [83, 48], [63, 92, 26, 10]], ![[69, 13, 106, 5], [76, 34, 39, 31], [30, 27], [91, 100, 90, 31], [25, 52], [36, 44, 101, 97]]]
 h' := ![![[30, 80, 52], [86, 33, 77], [79, 59, 24], [95, 60, 37], [19, 38, 23], [88, 74, 77], [0, 1]], ![[47, 26, 55], [68, 29, 80], [66, 25, 54], [78, 63, 16], [70, 52, 6], [16, 99, 72], [30, 80, 52]], ![[0, 1], [95, 45, 57], [41, 23, 29], [66, 91, 54], [34, 17, 78], [98, 41, 65], [47, 26, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 40], []]
 b := ![[], [53, 60, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [19, 33, 30, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1157205, -468981, -80571]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10815, -4383, -753]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1259, 652, -95]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-1259, 652, -95]] 
 ![![109, 0, 0], ![0, 109, 0], ![58, 31, 1]] where
  M :=![![![-1259, 652, -95], ![-25460, -6117, 1399], ![200196, 27841, -7516]]]
  hmulB := by decide  
  f := ![![![64457, 20693, 3037]], ![![813916, 261296, 38349]], ![![309190, 99261, 14568]]]
  g := ![![![39, 33, -95], ![-978, -454, 1399], ![5836, 2393, -7516]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [69, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 108], [0, 1]]
 g := ![![[103, 35], [12], [86, 94], [91, 64], [5], [87, 1]], ![[96, 74], [12], [89, 15], [100, 45], [5], [65, 108]]]
 h' := ![![[87, 108], [59, 97], [61, 11], [43, 58], [46, 8], [101, 88], [0, 1]], ![[0, 1], [105, 12], [37, 98], [75, 51], [88, 101], [18, 21], [87, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [24, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [69, 22, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107024, 95905, 26483]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13110, -6652, 26483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64457, -20693, -3037]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-64457, -20693, -3037]] 
 ![![109, 0, 0], ![48, 1, 0], ![23, 0, 1]] where
  M :=![![![-64457, -20693, -3037], ![-813916, -261296, -38349], ![-4731808, -1519079, -222947]]]
  hmulB := by decide  
  f := ![![![1259, -652, 95]], ![![788, -231, 29]], ![![-1571, -393, 89]]]
  g := ![![![9162, -20693, -3037], ![115691, -261296, -38349], ![672585, -1519079, -222947]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-1259, 652, -95]] ![![-64457, -20693, -3037]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [63, 27, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 64, 1], [42, 48, 112], [0, 1]]
 g := ![![[15, 107, 56], [103, 98], [10, 69], [43, 98], [71, 60, 1], [1]], ![[5, 102, 89, 52], [57, 41], [91, 77], [19, 49], [47, 101, 95, 102], [111, 14, 80, 1]], ![[67, 56, 55, 2], [59, 60], [78, 44], [87, 8], [12, 99, 100, 81], [55, 51, 30, 112]]]
 h' := ![![[72, 64, 1], [54, 98, 100], [92, 110, 18], [65, 72, 71], [47, 80, 95], [50, 86, 1], [0, 1]], ![[42, 48, 112], [56, 23, 39], [12, 55, 70], [35, 39, 90], [21, 14, 7], [22, 100, 21], [72, 64, 1]], ![[0, 1], [48, 105, 87], [6, 61, 25], [20, 2, 65], [90, 19, 11], [111, 40, 91], [42, 48, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 23], []]
 b := ![[], [78, 15, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [63, 27, 112, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![196055, 72772, 12091]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1735, 644, 107]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2857560239, 260602004, -83751904]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![2857560239, 260602004, -83751904]] 
 ![![127, 0, 0], ![0, 127, 0], ![7, 65, 1]] where
  M :=![![![2857560239, 260602004, -83751904], ![-22445510272, -1739448189, 604955912], ![92286847344, 6320966312, -2344404101]]]
  hmulB := by decide  
  f := ![![![-2000500218672335, -642231835878428, -94256891816896]], ![![-25260847006928128, -8109631779930731, -1190206779939960]], ![![-14195400330626183, -4557229202113145, -668839873533909]]]
  g := ![![![27116721, 44917132, -83751904], ![-210080328, -323319547, 604955912], ![855887213, 1249663251, -2344404101]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [114, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 126], [0, 1]]
 g := ![![[93, 8], [106, 84], [105, 15], [80, 21], [102, 61], [66, 1]], ![[113, 119], [62, 43], [79, 112], [69, 106], [64, 66], [5, 126]]]
 h' := ![![[66, 126], [108, 95], [95, 81], [24, 53], [56, 104], [96, 51], [0, 1]], ![[0, 1], [28, 32], [107, 46], [93, 74], [62, 23], [33, 76], [66, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [60, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [114, 61, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1454, 4557, 1768]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86, -869, 1768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2000500218672335, 642231835878428, 94256891816896]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![2000500218672335, 642231835878428, 94256891816896]] 
 ![![127, 0, 0], ![125, 1, 0], ![126, 0, 1]] where
  M :=![![![2000500218672335, 642231835878428, 94256891816896], ![25260847006928128, 8109631779930731, 1190206779939960], ![146857285008490576, 47146420121722904, 6919424999990771]]]
  hmulB := by decide  
  f := ![![![-2857560239, -260602004, 83751904]], ![![-2635822989, -242801593, 77669544]], ![![-3561727854, -308321408, 101552315]]]
  g := ![![![-709880690039843, 642231835878428, 94256891816896], ![-8963851809109041, 8109631779930731, 1190206779939960], ![-52112541576422910, 47146420121722904, 6919424999990771]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![2857560239, 260602004, -83751904]] ![![2000500218672335, 642231835878428, 94256891816896]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![726848501010924567, 44559661199661009, -17565865862970689]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![726848501010924567, 44559661199661009, -17565865862970689]] 
 ![![131, 0, 0], ![0, 131, 0], ![33, 78, 1]] where
  M :=![![![726848501010924567, 44559661199661009, -17565865862970689], ![-4707652051276144652, -247412057841714386, 106685188262292707], ![16649641252785295064, 740044433968416177, -354097246104007093]]]
  hmulB := by decide  
  f := ![![![66077470032779031443516151574189, 21213221819849407218210920817564, 3113349794356596525882739735339]], ![![834377744887567868936574249070852, 267864979925311037162925977041415, 39313093845342217910539101899789]], ![![550479284848428054047578450072603, 176723460673190836570863417372819, 25936746177331522913195169729705]]]
  g := ![![![9973450950297384, 10799215255812021, -17565865862970689], ![-62811169953677893, -65411120170233172, 106685188262292707], ![216296567742118543, 216485722367030301, -354097246104007093]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [2, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 130], [0, 1]]
 g := ![![[80, 41], [90, 38], [49], [91], [3], [55], [1]], ![[70, 90], [36, 93], [49], [91], [3], [55], [1]]]
 h' := ![![[102, 130], [82, 98], [66, 13], [66, 124], [95, 109], [25, 93], [129, 102], [0, 1]], ![[0, 1], [122, 33], [82, 118], [7, 7], [78, 22], [79, 38], [53, 29], [102, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [83, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [2, 29, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16144, 9148, 1958]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-370, -1096, 1958]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-168066328121319879, -6588650329660022, 3422721685810713]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-168066328121319879, -6588650329660022, 3422721685810713]] 
 ![![131, 0, 0], ![107, 1, 0], ![117, 0, 1]] where
  M :=![![![-168066328121319879, -6588650329660022, 3422721685810713], ![917289411797271084, 23862879326041453, -16600022345130757], ![-2683047700146156980, -22755942110156411, 40462901671172210]]]
  hmulB := by decide  
  f := ![![![587812192247565116090204044788003, 188708653893284291751543744957577, 27695748141483280725285596010665]], ![![536781412766465546992582996360111, 172325955762811442040637351670419, 25291348173922109468575272267524]], ![![854393017056853355248786695862357, 274290595314354927730344602661800, 40256146650804108641136833570286]]]
  g := ![![![1041685648186634, -6588650329660022, 3422721685810713], ![2337129299932322, 23862879326041453, -16600022345130757], ![-38032987709057783, -22755942110156411, 40462901671172210]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![726848501010924567, 44559661199661009, -17565865862970689]] ![![-168066328121319879, -6588650329660022, 3422721685810713]]
  ![![131, 0, 0]] where
 M := ![![![-34154597248949426127572360335844417, -3325900971089185114626548617317218, 1037342851920889156003091402579768]]]
 hmul := by decide  
 g := ![![![![-260722116404194092576888246838507, -25388557031215153546767546697078, 7918647724586940122161003073128]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-831, -266, -39]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-831, -266, -39]] 
 ![![137, 0, 0], ![0, 137, 0], ![74, 56, 1]] where
  M :=![![![-831, -266, -39], ![-10452, -3359, -493], ![-60836, -19523, -2866]]]
  hmulB := by decide  
  f := ![![![-15, 7, -1]], ![![-268, -66, 15]], ![![-102, -21, 5]]]
  g := ![![![15, 14, -39], ![190, 177, -493], ![1104, 1029, -2866]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [34, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 136], [0, 1]]
 g := ![![[127, 133], [115], [87], [117, 11], [60], [109], [1]], ![[0, 4], [115], [87], [21, 126], [60], [109], [1]]]
 h' := ![![[66, 136], [48, 74], [81, 72], [132, 19], [84, 82], [53, 103], [103, 66], [0, 1]], ![[0, 1], [0, 63], [38, 65], [16, 118], [16, 55], [1, 34], [75, 71], [66, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [28, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [34, 71, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![858, 105, 156]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-78, -63, 156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 7, -1]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-15, 7, -1]] 
 ![![137, 0, 0], ![26, 1, 0], ![60, 0, 1]] where
  M :=![![![-15, 7, -1], ![-268, -66, 15], ![2144, 301, -81]]]
  hmulB := by decide  
  f := ![![![-831, -266, -39]], ![![-234, -75, -11]], ![![-808, -259, -38]]]
  g := ![![![-1, 7, -1], ![4, -66, 15], ![-6, 301, -81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-831, -266, -39]] ![![-15, 7, -1]]
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


lemma PB165I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB165I2 : PrimesBelowBoundCertificateInterval O 79 137 165 where
  m := 11
  g := ![3, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB165I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
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
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
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
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
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
  β := ![I83N0, I83N1, I83N2, I89N1, I101N1, I103N1, I109N1, I127N1, I131N1, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [], [I101N1], [I103N1], [], [I109N1], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
