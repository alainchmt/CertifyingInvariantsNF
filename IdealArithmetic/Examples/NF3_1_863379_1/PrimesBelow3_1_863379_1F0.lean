
import IdealArithmetic.Examples.NF3_1_863379_1.RI3_1_863379_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-233395955432550279513045172601792904660505, -6753765246519192040432648405474358512837, -4116974424713774563845993928275154203689]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-233395955432550279513045172601792904660505, -6753765246519192040432648405474358512837, -4116974424713774563845993928275154203689]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![-233395955432550279513045172601792904660505, -6753765246519192040432648405474358512837, -4116974424713774563845993928275154203689], ![-382878621498381034437677435329589340943077, -11079336498006453065361500474934577661299, -6753765246519192040432648405474358512837], ![-628100167926284859760236301709115341693841, -18175298186344664254314421433973981249879, -11079336498006453065361500474934577661299]]]
  hmulB := by decide  
  f := ![![![-102395405691718085339, 64498055000978495816, -1267716337997728279]], ![![-117897619433788729947, -33938723439840758273, 64498055000978495816]], ![![2889013044982746647801, -1785116628962744883234, 14645807611570004632]]]
  g := ![![![-114639490503918252474599589336758875228408, -1318395410902708738293327238599602154574, -4116974424713774563845993928275154203689], ![-188062428125930921198622393462057491215120, -2162785625743630512464426034730109574231, -6753765246519192040432648405474358512837], ![-308510415714139203347437400617090382016271, -3547980844169105594476460479519701794290, -11079336498006453065361500474934577661299]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1115, 1487, -485]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-315, 986, -485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-102395405691718085339, 64498055000978495816, -1267716337997728279]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-102395405691718085339, 64498055000978495816, -1267716337997728279]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-102395405691718085339, 64498055000978495816, -1267716337997728279], ![-117897619433788729947, -33938723439840758273, 64498055000978495816], ![5998319115091000110888, -3600792589486627504011, -33938723439840758273]]]
  hmulB := by decide  
  f := ![![![-233395955432550279513045172601792904660505, -6753765246519192040432648405474358512837, -4116974424713774563845993928275154203689]], ![![-308137288465465656975361303965691122801791, -8916550872262822552897074440204468087068, -5435369835616483302139321166874756358263]], ![![-430748061679417569636640737155454123177173, -12464531716431928147373534919724169881358, -7598155461360113814603747201604865932494]]]
  g := ![![![-82812872177349426438, 64498055000978495816, -1267716337997728279], ![-74228475497463233745, -33938723439840758273, 64498055000978495816], ![4816525214008734186586, -3600792589486627504011, -33938723439840758273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-233395955432550279513045172601792904660505, -6753765246519192040432648405474358512837, -4116974424713774563845993928275154203689]] ![![-102395405691718085339, 64498055000978495816, -1267716337997728279]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-832157645901, 751237778026, -148719361660]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-832157645901, 751237778026, -148719361660]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-832157645901, 751237778026, -148719361660], ![-13830900634380, 7198687883739, 751237778026], ![69865113356418, -54397740647784, 7198687883739]]]
  hmulB := by decide  
  f := ![![![92686745061366556421414505, 2682070974401896796642226, 1634942465992682022503416]], ![![50683216445773142697605896, 1466617299253909068743347, 894023658133965598880742]], ![![83144200206458800695909006, 2405938906539000358045828, 1466617299253909068743347]]]
  g := ![![![-277385881967, 751237778026, -148719361660], ![-4610300211460, 7198687883739, 751237778026], ![23288371118806, -54397740647784, 7198687883739]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-832157645901, 751237778026, -148719361660]] ![![-832157645901, 751237778026, -148719361660]]
  ![![-20088103773708555946165959, 12872775294493431803709228, -382468113826913690034404]] where
 M := ![![![-20088103773708555946165959, 12872775294493431803709228, -382468113826913690034404]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-20088103773708555946165959, 12872775294493431803709228, -382468113826913690034404]] ![![-832157645901, 751237778026, -148719361660]]
  ![![3, 0, 0]] where
 M := ![![![-188046784967628798511503141976492179453, 98381550360851664564561832681032387294, 9904736502526694756808509429751399312]]]
 hmul := by decide  
 g := ![![![![-62682261655876266170501047325497393151, 32793850120283888188187277560344129098, 3301578834175564918936169809917133104]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [1, 3, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 4], [4, 4, 1], [0, 1]]
 g := ![![[3, 1, 1], []], ![[4, 1, 1, 4], [1, 1]], ![[1, 1], [4, 1]]]
 h' := ![![[2, 0, 4], [0, 0, 1], [0, 1]], ![[4, 4, 1], [3, 1, 4], [2, 0, 4]], ![[0, 1], [2, 4], [4, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 4], []]
 b := ![[], [3, 2, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [1, 3, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-234605, -7550, -4290]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46921, -1510, -858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [3, 3, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 6], [1, 5, 1], [0, 1]]
 g := ![![[1, 4, 4], [1]], ![[1, 3], [3, 2, 5, 6]], ![[6, 3, 4, 4], [1, 0, 6, 1]]]
 h' := ![![[4, 1, 6], [4, 4, 5], [0, 1]], ![[1, 5, 1], [6, 5], [4, 1, 6]], ![[0, 1], [5, 5, 2], [1, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [4, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [3, 3, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-371805, 354844, -78190]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53115, 50692, -11170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀


def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10091, 292, 178]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![10091, 292, 178]] 
 ![![11, 0, 0], ![2, 1, 0], ![7, 0, 1]] where
  M :=![![![10091, 292, 178], ![16554, 479, 292], ![27156, 786, 479]]]
  hmulB := by decide  
  f := ![![![-71, 40, 2]], ![![4, -9, 4]], ![![293, -154, -15]]]
  g := ![![![751, 292, 178], ![1232, 479, 292], ![2021, 786, 479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1811, 1268, -100]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-1811, 1268, -100]] 
 ![![11, 0, 0], ![7, 1, 0], ![6, 0, 1]] where
  M :=![![![-1811, 1268, -100], ![-9300, 3589, 1268], ![117924, -77772, 3589]]]
  hmulB := by decide  
  f := ![![![-111495817, -3226348, -1966724]], ![![-87579641, -2534287, -1544856]], ![![-88093206, -2549148, -1553915]]]
  g := ![![![-917, 1268, -100], ![-3821, 3589, 1268], ![58254, -77772, 3589]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![10091, 292, 178]] ![![10091, 292, 178]]
  ![![111495817, 3226348, 1966724]] where
 M := ![![![111495817, 3226348, 1966724]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI11N1 : IdealMulLeCertificate' Table 
  ![![111495817, 3226348, 1966724]] ![![-1811, 1268, -100]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 0, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 9], [0, 11, 4], [0, 1]]
 g := ![![[10, 10, 10], [12, 3], [1]], ![[9, 11, 11, 10], [0, 12], [4, 11, 0, 1]], ![[0, 9, 0, 12], [1, 3], [11, 12, 4, 12]]]
 h' := ![![[4, 1, 9], [6, 9, 7], [3, 0, 4], [0, 1]], ![[0, 11, 4], [4, 11, 2], [11, 3, 5], [4, 1, 9]], ![[0, 1], [0, 6, 4], [7, 10, 4], [0, 11, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 10], []]
 b := ![[], [4, 1, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 0, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8008, 936, -3510]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![616, 72, -270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀


def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4837220, 3220131, -165470]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-4837220, 3220131, -165470]] 
 ![![17, 0, 0], ![8, 1, 0], ![4, 0, 1]] where
  M :=![![![-4837220, 3220131, -165470], ![-15388710, 4098160, 3220131], ![299472183, -189275784, 4098160]]]
  hmulB := by decide  
  f := ![![![-626287734993304, -18122851919520, -11047366192361]], ![![-355159231519765, -10277222115410, -6264810674024]], ![![-246504480499328, -7133085877269, -4348201492662]]]
  g := ![![![-1760964, 3220131, -165470], ![-3591442, 4098160, 3220131], ![105722695, -189275784, 4098160]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23916176, 692061, 421868]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![23916176, 692061, 421868]] 
 ![![17, 0, 0], ![13, 1, 0], ![1, 0, 1]] where
  M :=![![![23916176, 692061, 421868], ![39233724, 1135304, 692061], ![64361673, 1862430, 1135304]]]
  hmulB := by decide  
  f := ![![![4186, -2304, -151]], ![![2375, -1036, -251]], ![![-12358, 6357, 717]]]
  g := ![![![852795, 692061, 421868], ![1398983, 1135304, 692061], ![2294987, 1862430, 1135304]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-4837220, 3220131, -165470]] ![![23916176, 692061, 421868]]
  ![![-4186, 2304, 151]] where
 M := ![![![-4186, 2304, 151]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-4186, 2304, 151]] ![![23916176, 692061, 421868]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -9, 4]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![4, -9, 4]] 
 ![![19, 0, 0], ![2, 1, 0], ![15, 0, 1]] where
  M :=![![![4, -9, 4], ![372, -212, -9], ![-837, 858, -212]]]
  hmulB := by decide  
  f := ![![![52666, 1524, 929]], ![![10091, 292, 178]], ![![49038, 1419, 865]]]
  g := ![![![-2, -9, 4], ![49, -212, -9], ![33, 858, -212]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74741333032915377462316131363898218141286, 2162785625743630512464426034730109574231, 1318395410902708738293327238599602154574]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![74741333032915377462316131363898218141286, 2162785625743630512464426034730109574231, 1318395410902708738293327238599602154574]] 
 ![![19, 0, 0], ![18, 1, 0], ![18, 0, 1]] where
  M :=![![![74741333032915377462316131363898218141286, 2162785625743630512464426034730109574231, 1318395410902708738293327238599602154574], ![122610773213951912661279433189763000375382, 3547980844169105594476460479519701794290, 2162785625743630512464426034730109574231], ![201139063194157637659191621229900190403483, 5820349423795864988200427314337083366908, 3547980844169105594476460479519701794290]]]
  hmulB := by decide  
  f := ![![![-124337091306358343648, 43669143936325496202, 19582533514368658901]], ![![-21941685614640258309, -20828911064652999614, 20850249852366387180]], ![![95955933819148471638, 13109812375187758659, -43647805148612108636]]]
  g := ![![![635793388067435313088240654945442474884, 2162785625743630512464426034730109574231, 1318395410902708738293327238599602154574], ![1042998776606455933491761891224547144316, 3547980844169105594476460479519701794290, 2162785625743630512464426034730109574231], ![1711006230041482482684612681077792500101, 5820349423795864988200427314337083366908, 3547980844169105594476460479519701794290]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![4, -9, 4]] ![![74741333032915377462316131363898218141286, 2162785625743630512464426034730109574231, 1318395410902708738293327238599602154574]]
  ![![24625982724846534516111667326630800638, 712600636031652371269080591455615946, 434388594582718899316559906229627377]] where
 M := ![![![24625982724846534516111667326630800638, 712600636031652371269080591455615946, 434388594582718899316559906229627377]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![24625982724846534516111667326630800638, 712600636031652371269080591455615946, 434388594582718899316559906229627377]] ![![74741333032915377462316131363898218141286, 2162785625743630512464426034730109574231, 1318395410902708738293327238599602154574]]
  ![![19, 0, 0]] where
 M := ![![![2015323806053765364435898456682898402978255743604733807462502756581162780935931, 58317308269475094426350996732236456645633094805936171884403172675595571548034, 35549187438417106594692929375986120128561748626396086327305693173228374383068]]]
 hmul := by decide  
 g := ![![![![106069674002829756022942024035942021209381881242354410919079092451640146365049, 3069332014182899706650052459591392455033320779259798520231745930294503765686, 1871009865179847715510154177683480006766407822441899280384510167012019704372]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8679687830179728973797287, -251163624105921340844468, -153104850275249175258068]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-8679687830179728973797287, -251163624105921340844468, -153104850275249175258068]] 
 ![![23, 0, 0], ![10, 1, 0], ![15, 0, 1]] where
  M :=![![![-8679687830179728973797287, -251163624105921340844468, -153104850275249175258068], ![-14238751075598173299000324, -412025915316273509861615, -251163624105921340844468], ![-23358217041850684698535524, -675915373878420893399052, -412025915316273509861615]]]
  hmulB := by decide  
  f := ![![![-3079859763889, 1790111744284, 53226056796]], ![![-1123851058994, 519436983129, 100972709228]], ![![5229673728699, -2820188467176, -224159825171]]]
  g := ![![![-168325166738772953760069, -251163624105921340844468, -153104850275249175258068], ![-276132067862896438596398, -412025915316273509861615, -251163624105921340844468], ![-452985851014016222461773, -675915373878420893399052, -412025915316273509861615]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97888153178, -8797243366, -31011650081]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![97888153178, -8797243366, -31011650081]] 
 ![![23, 0, 0], ![15, 1, 0], ![5, 0, 1]] where
  M :=![![![97888153178, -8797243366, -31011650081], ![-2884083457533, 1772517257552, -8797243366], ![-818143633038, -2409032315769, 1772517257552]]]
  hmulB := by decide  
  f := ![![![3120624584761284648594250, 90301332895569171827321, 55046076444577009671668]], ![![2257767560033257896886038, 65332889138594074075391, 39825759981053231169667]], ![![1043528125351928531430961, 30196512933164020866365, 18407253868565703247066]]]
  g := ![![![16735002351, -8797243366, -31011650081], ![-1279472004521, 1772517257552, -8797243366], ![1150206731119, -2409032315769, 1772517257552]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![2, -1, 0]] 
 ![![23, 0, 0], ![21, 1, 0], ![19, 0, 1]] where
  M :=![![![2, -1, 0], ![0, 2, -1], ![-93, 54, 2]]]
  hmulB := by decide  
  f := ![![![58, 2, 1]], ![![57, 2, 1]], ![![56, 1, 1]]]
  g := ![![![1, -1, 0], ![-1, 2, -1], ![-55, 54, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-8679687830179728973797287, -251163624105921340844468, -153104850275249175258068]] ![![97888153178, -8797243366, -31011650081]]
  ![![-58, -2, -1]] where
 M := ![![![-58, -2, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-58, -2, -1]] ![![2, -1, 0]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [3, 18, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 0, 10], [20, 28, 19], [0, 1]]
 g := ![![[3, 14, 22], [13, 7], [13, 7, 5], [1]], ![[22, 20, 24, 15], [16, 5], [21, 1, 3, 19], [23, 18, 9, 14]], ![[14, 10, 26, 8], [25, 25], [7, 8, 5, 17], [11, 10, 10, 15]]]
 h' := ![![[20, 0, 10], [3, 25, 14], [19, 15, 23], [26, 11, 11], [0, 1]], ![[20, 28, 19], [10, 16, 4], [0, 18, 11], [14, 25, 12], [20, 0, 10]], ![[0, 1], [11, 17, 11], [12, 25, 24], [21, 22, 6], [20, 28, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 2], []]
 b := ![[], [18, 1, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [3, 18, 18, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![434536, -153555, -43761]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14984, -5295, -1509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11856511528634324391066524, -188391457648261105230619, -4290925098164477267903076]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![11856511528634324391066524, -188391457648261105230619, -4290925098164477267903076]] 
 ![![31, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![11856511528634324391066524, -188391457648261105230619, -4290925098164477267903076], ![-399056034129296385914986068, 243566466829516096857832628, -188391457648261105230619], ![-17520405561288282786447567, -388882895416290286232532642, 243566466829516096857832628]]]
  hmulB := by decide  
  f := ![![![-59251361548291813887502808763520141194865243806020986, -1714553217908880918497106458110346154047770505043524, -1045160956931331090776878850240111810563452909486889]], ![![-3135482870793993272330636550720335431690358728460667, -90731286258062418888753253243680755627057635281580, -55308168319641319951519563164849875937024855001404]], ![![-5143659653726642755491319374331038462143311515130572, -148841781533361994948580139818442131091016558384851, -90731286258062418888753253243680755627057635281580]]]
  g := ![![![382468113826913690034404, -188391457648261105230619, -4290925098164477267903076], ![-12872775294493431803709228, 243566466829516096857832628, -188391457648261105230619], ![-565174372944783315691857, -388882895416290286232532642, 243566466829516096857832628]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84030728046226, -2431592311300, -1482255155687]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-84030728046226, -2431592311300, -1482255155687]] 
 ![![31, 0, 0], ![15, 1, 0], ![23, 0, 1]] where
  M :=![![![-84030728046226, -2431592311300, -1482255155687], ![-137849729478891, -3988949639128, -2431592311300], ![-226138084950900, -6543744668691, -3988949639128]]]
  hmulB := by decide  
  f := ![![![6907916, -2949317, -769064]], ![![1035348, 135407, -467267]], ![![-3722723, 642125, 991900]]]
  g := ![![![-434354025675, -2431592311300, -1482255155687], ![-712543926841, -3988949639128, -2431592311300], ![-1168905587761, -6543744668691, -3988949639128]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![643976149533599114937505992261314802751, 18634700546746078665719313911572016260, 11359379955158082775808194959948484984]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![643976149533599114937505992261314802751, 18634700546746078665719313911572016260, 11359379955158082775808194959948484984]] 
 ![![31, 0, 0], ![16, 1, 0], ![23, 0, 1]] where
  M :=![![![643976149533599114937505992261314802751, 18634700546746078665719313911572016260, 11359379955158082775808194959948484984], ![1056422335829701698150162131275209103512, 30569631955062645043863464424096613615, 18634700546746078665719313911572016260], ![1733027150847385315911896193776197512180, 50148506305413450201319180050320225472, 30569631955062645043863464424096613615]]]
  hmulB := by decide  
  f := ![![![-454528458246806495, 4358596835968932548, -2488024242373069560]], ![![-7698668060407883000, 6568913871141995823, -1143541646516134852]], ![![12738559716304328309, -11822669563088141228, 2473362034042527415]]]
  g := ![![![2727587155387933949755112438624109289, 18634700546746078665719313911572016260, 11359379955158082775808194959948484984], ![4474519741081921552800080016887319732, 30569631955062645043863464424096613615, 18634700546746078665719313911572016260], ![7340306935300944409094504232801670693, 50148506305413450201319180050320225472, 30569631955062645043863464424096613615]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![11856511528634324391066524, -188391457648261105230619, -4290925098164477267903076]] ![![-84030728046226, -2431592311300, -1482255155687]]
  ![![-454528458246806495, 4358596835968932548, -2488024242373069560]] where
 M := ![![![-454528458246806495, 4358596835968932548, -2488024242373069560]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-454528458246806495, 4358596835968932548, -2488024242373069560]] ![![643976149533599114937505992261314802751, 18634700546746078665719313911572016260, 11359379955158082775808194959948484984]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB263I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB263I0 : PrimesBelowBoundCertificateInterval O 1 31 263 where
  m := 11
  g := ![2, 3, 1, 1, 3, 1, 3, 3, 3, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB263I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1, I17N1]
    · exact ![I19N0, I19N1, I19N1]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
    · exact ![24389]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I5N0, I11N0, I11N1, I17N0, I17N1, I19N0, I19N1, I23N0, I23N1, I23N2, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N0], [I5N0], [], [I11N0, I11N0, I11N1], [], [I17N0, I17N1, I17N1], [I19N0, I19N1, I19N1], [I23N0, I23N1, I23N2], [], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
