
import IdealArithmetic.Examples.NF3_1_342171_1.RI3_1_342171_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24253453377, -4109321764, -915446311]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![24253453377, -4109321764, -915446311]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 0, 1]] where
  M :=![![![24253453377, -4109321764, -915446311], ![-97016935695, 33875826278, -27849806037], ![-369309929156, 46992685484, 42094469806]]]
  hmulB := by decide  
  f := ![![![-1367361061149858914488, -64980220173762804130, -72727657134647324863]], ![![-7184543182408316119971, -341426424303911845673, -382133884081692304047]], ![![-2671578694848068259741, -126959715860838969994, -142096820545516781138]]]
  g := ![![![12584449844, -2054660882, -915446311], ![-34583564829, 16937913139, -27849806037], ![-205702199481, 23496342742, 42094469806]]]
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
  c := ![-6853, 4654, -4727]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1063, 2327, -4727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1367361061149858914488, 64980220173762804130, 72727657134647324863]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1367361061149858914488, 64980220173762804130, 72727657134647324863]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![1367361061149858914488, 64980220173762804130, 72727657134647324863], ![7184543182408316119971, 341426424303911845673, 382133884081692304047], ![3975796328546277604994, 188939211547915135858, 211465983956386237413]]]
  hmulB := by decide  
  f := ![![![-24253453377, 4109321764, 915446311]], ![![36381741159, -14883252257, 14382626174]], ![![184654964578, -23496342742, -21047234903]]]
  g := ![![![651190420488048055179, 64980220173762804130, 72727657134647324863], ![3421558379052202137149, 341426424303911845673, 382133884081692304047], ![1893428558499181234568, 188939211547915135858, 211465983956386237413]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![24253453377, -4109321764, -915446311]] ![![1367361061149858914488, 64980220173762804130, 72727657134647324863]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103341424, -11867591, -14095747]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![103341424, -11867591, -14095747]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![103341424, -11867591, -14095747], ![-1391022641, 302910038, -68977390], ![-700092423, -47518087, 326645220]]]
  hmulB := by decide  
  f := ![![![95666442383665430, 4546294805341009, 5088338712175876]], ![![167553814897247330, 7962552168789433, 8911908308403729]], ![![156498880698593567, 7437195641793633, 8323914773346011]]]
  g := ![![![43844306, -11867591, -14095747], ![-417689287, 302910038, -68977390], ![-451127621, -47518087, 326645220]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![103341424, -11867591, -14095747]] ![![103341424, -11867591, -14095747]]
  ![![37055863360700588, -4151423261892053, -5242387494435578]] where
 M := ![![![37055863360700588, -4151423261892053, -5242387494435578]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![37055863360700588, -4151423261892053, -5242387494435578]] ![![103341424, -11867591, -14095747]]
  ![![3, 0, 0]] where
 M := ![![![13274285200194445441954779, -1448163383482183966672236, -1948376549853563105154726]]]
 hmul := by decide  
 g := ![![![![4424761733398148480651593, -482721127827394655557412, -649458849951187701718242]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 3, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 1], [1, 4, 4], [0, 1]]
 g := ![![[3, 4, 1], []], ![[4, 4, 1, 1], [4, 1]], ![[1, 4], [1, 1]]]
 h' := ![![[3, 0, 1], [0, 0, 1], [0, 1]], ![[1, 4, 4], [3, 4, 4], [3, 0, 1]], ![[0, 1], [2, 1], [1, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 4], []]
 b := ![[], [2, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 3, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-279180, 94000, -85715]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55836, 18800, -17143]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23779069870083530, 1130037441892585, 1264769115948023]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![23779069870083530, 1130037441892585, 1264769115948023]] 
 ![![7, 0, 0], ![1, 1, 0], ![0, 0, 7]] where
  M :=![![![23779069870083530, 1130037441892585, 1264769115948023], ![124942679130743401, 5937570572755770, 6645492977300072], ![69141020153244009, 3285744226779593, 3677495688970600]]]
  hmulB := by decide  
  f := ![![![-8095528, 6013377, -8082370]], ![![-111436952, 17880968, 6013377]], ![![841933409, -219518575, 107126645]]]
  g := ![![![3235576061170135, 1130037441892585, 180681302278289], ![17000729793998233, 5937570572755770, 949356139614296], ![9407896560923488, 3285744226779593, 525356526995800]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[5, 2], [3, 1]], ![[4, 5], [6, 6]]]
 h' := ![![[3, 6], [6, 4], [0, 1]], ![[0, 1], [4, 3], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38448, -4049, 1267]
  a := ![3, 21, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6071, -4049, 181]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8095528, -6013377, 8082370]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![8095528, -6013377, 8082370]] 
 ![![7, 0, 0], ![5, 1, 0], ![1, 0, 1]] where
  M :=![![![8095528, -6013377, 8082370], ![771963136, -119153399, -50176009], ![-841933409, 219518575, -107126645]]]
  hmulB := by decide  
  f := ![![![-23779069870083530, -1130037441892585, -1264769115948023]], ![![-34834004068737293, -1655393968888385, -1852762651005741]], ![![-13274298574761077, -630825952667454, -706037829274089]]]
  g := ![![![4297149, -6013377, 8082370], ![202558020, -119153399, -50176009], ![-261771377, 219518575, -107126645]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![23779069870083530, 1130037441892585, 1264769115948023]] ![![8095528, -6013377, 8082370]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11581113063, 2321960150, -212953544]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-11581113063, 2321960150, -212953544]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 7, 1]] where
  M :=![![![-11581113063, 2321960150, -212953544], ![-16012573468, -6064849753, 16466674594], ![232044647958, -38236658954, -10708770053]]]
  hmulB := by decide  
  f := ![![![63143427451649569235, 3000724486686638266, 3358493723777868588]], ![![331775340179826529568, 15766746081668178681, 17646577683028599274]], ![![245041467241949684697, 11644948028353044453, 13033347460075336621]]]
  g := ![![![-994750221, 346603178, -212953544], ![-5946599750, -11030142901, 16466674594], ![24015541647, 3338611947, -10708770053]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [4, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[8, 3], [4, 1], [1]], ![[0, 8], [5, 10], [1]]]
 h' := ![![[1, 10], [6, 5], [7, 1], [0, 1]], ![[0, 1], [0, 6], [8, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [8, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [4, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5155, 1905, -1513]
  a := ![-3, 1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, 1136, -1513]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63143427451649569235, -3000724486686638266, -3358493723777868588]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-63143427451649569235, -3000724486686638266, -3358493723777868588]] 
 ![![11, 0, 0], ![7, 1, 0], ![8, 0, 1]] where
  M :=![![![-63143427451649569235, -3000724486686638266, -3358493723777868588], ![-331775340179826529568, -15766746081668178681, -17646577683028599274], ![-183598476047712116986, -8725032280146323418, -9765297108294902149]]]
  hmulB := by decide  
  f := ![![![11581113063, -2321960150, 212953544]], ![![8825487719, -926261027, -1361454526]], ![![-12672340314, 1787361614, 1128399855]]]
  g := ![![![-1388218750420013879, -3000724486686638266, -3358493723777868588], ![-7294136013083680419, -15766746081668178681, -17646577683028599274], ![-4036443020029875988, -8725032280146323418, -9765297108294902149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-11581113063, 2321960150, -212953544]] ![![-63143427451649569235, -3000724486686638266, -3358493723777868588]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10951690399197439862832264713, -520450138324320621177426158, -582502169344975338461086016]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-10951690399197439862832264713, -520450138324320621177426158, -582502169344975338461086016]] 
 ![![13, 0, 0], ![0, 13, 0], ![5, 9, 1]] where
  M :=![![![-10951690399197439862832264713, -520450138324320621177426158, -582502169344975338461086016], ![-57543610703111249073080195868, -2734607997347130407093400631, -3060648798925269009780897090], ![-31843593998419889423455584814, -1513282634654796097715983886, -1693707720698489164738548315]]]
  hmulB := by decide  
  f := ![![![46066878408075, -9220037547262, 817874430452]], ![![60893744659320, 24578724404033, -65358137261286]], ![![-10933656144971, 25114991230473, -41624235669289]]]
  g := ![![![-618398427113274090040525741, 363236106598496724997872922, -582502169344975338461086016], ![-3249258977575761848013516186, 1908556245613868513918051783, -3060648798925269009780897090], ![-1798081184225187969212526403, 1056160527048585106533150073, -1693707720698489164738548315]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[3, 12], [1], [6, 1]], ![[10, 1], [1], [12, 12]]]
 h' := ![![[6, 12], [3, 8], [12, 12], [0, 1]], ![[0, 1], [12, 5], [6, 1], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [11, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1949, 1930, -2751]
  a := ![4, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1208, 2053, -2751]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![162171265875254591976593, 7706760753864222443038, 8625619492008206235470]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![162171265875254591976593, 7706760753864222443038, 8625619492008206235470]] 
 ![![13, 0, 0], ![3, 1, 0], ![6, 0, 1]] where
  M :=![![![162171265875254591976593, 7706760753864222443038, 8625619492008206235470], ![852098612232524449726666, 40493734248995720887581, 45321705785041350865796], ![471535969380566977439646, 22408500564167963121950, 25080212741267276001505]]]
  hmulB := by decide  
  f := ![![![227659987205, -81239205690, 68507830178]], ![![551212390577, -86531868325, -33204521498]], ![![-669730276492, 140559856466, -23667021439]]]
  g := ![![![6715174358585591325743, 7706760753864222443038, 8625619492008206235470], ![35283628828868398605319, 40493734248995720887581, 45321705785041350865796], ![19525322403112264004982, 22408500564167963121950, 25080212741267276001505]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-10951690399197439862832264713, -520450138324320621177426158, -582502169344975338461086016]] ![![162171265875254591976593, 7706760753864222443038, 8625619492008206235470]]
  ![![13, 0, 0]] where
 M := ![![![-2494195061202466239734758726442777367978306028982373, -118530027538560473473299711042662658476438874313092, -132662080552097182713082278784867101962308758315958]]]
 hmul := by decide  
 g := ![![![![-191861158554035864594981440495598259075254309921721, -9117694426043113344099977772512512190495298024084, -10204775427084398670237098368066700150946827562766]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7027348, 4100333, -4992735]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-7027348, 4100333, -4992735]] 
 ![![17, 0, 0], ![0, 17, 0], ![15, 10, 1]] where
  M :=![![![-7027348, 4100333, -4992735], ![-476094629, 71964010, 33695066], ![557499821, -141388755, 63763344]]]
  hmulB := by decide  
  f := ![![![-550162903331310, -26145037770669, -29262248383784]], ![![-2890728168768386, -137374215345219, -153753016010899]], ![![-2279964820772195, -108349301623102, -121267530921743]]]
  g := ![![![3991981, 3178099, -4992735], ![-57736507, -15587450, 33695066], ![-23467667, -45824835, 63763344]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [6, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[16, 9], [13], [2], [1]], ![[2, 8], [13], [2], [1]]]
 h' := ![![[6, 16], [5, 3], [7, 8], [11, 6], [0, 1]], ![[0, 1], [6, 14], [4, 9], [13, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [9, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [6, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7376, 1370, -3365]
  a := ![-5, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3403, 2060, -3365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-550162903331310, -26145037770669, -29262248383784]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-550162903331310, -26145037770669, -29262248383784]] 
 ![![17, 0, 0], ![16, 1, 0], ![10, 0, 1]] where
  M :=![![![-550162903331310, -26145037770669, -29262248383784], ![-2890728168768386, -137374215345219, -153753016010899], ![-1599676715473805, -76020407580509, -85084139803881]]]
  hmulB := by decide  
  f := ![![![-7027348, 4100333, -4992735]], ![![-34619541, 8092314, -2716982]], ![![28660373, -5905025, 813882]]]
  g := ![![![9457657931602, -26145037770669, -29262248383784], ![49693496286124, -137374215345219, -153753016010899], ![27499482579597, -76020407580509, -85084139803881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-7027348, 4100333, -4992735]] ![![-550162903331310, -26145037770669, -29262248383784]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26097578728, -1240218447, -1388086740]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-26097578728, -1240218447, -1388086740]] 
 ![![19, 0, 0], ![2, 1, 0], ![13, 0, 1]] where
  M :=![![![-26097578728, -1240218447, -1388086740], ![-137124850674, -6516496075, -7293442389], ![-75882413679, -3606111135, -4036059181]]]
  hmulB := by decide  
  f := ![![![-313060, 62007, -4383]], ![![-48803, -3226, 22614]], ![![109745, -10218, -19279]]]
  g := ![![![-293263906, -1240218447, -1388086740], ![-1540900393, -6516496075, -7293442389], ![-852706424, -3606111135, -4036059181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2755625344, -1395699123, 1574408070]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![2755625344, -1395699123, 1574408070]] 
 ![![19, 0, 0], ![15, 1, 0], ![4, 0, 1]] where
  M :=![![![2755625344, -1395699123, 1574408070], ![149926184544, -22256194829, -11344301931], ![-185763873171, 46126015965, -19464796583]]]
  hmulB := by decide  
  f := ![![![956479757039187797722, 45454172251978340841, 50873565002413776543]], ![![1019623184490837366957, 48454896738664979107, 54232058726191645131]], ![![347737876659021547531, 16525323435097825023, 18495598408455679732]]]
  g := ![![![915446311, -1395699123, 1574408070], ![27849806037, -22256194829, -11344301931], ![-42094469806, 46126015965, -19464796583]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-26097578728, -1240218447, -1388086740]] ![![-26097578728, -1240218447, -1388086740]]
  ![![956479757039187797722, 45454172251978340841, 50873565002413776543]] where
 M := ![![![956479757039187797722, 45454172251978340841, 50873565002413776543]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![956479757039187797722, 45454172251978340841, 50873565002413776543]] ![![2755625344, -1395699123, 1574408070]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![296745028722, 14102023123, 15783373769]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![296745028722, 14102023123, 15783373769]] 
 ![![23, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![296745028722, 14102023123, 15783373769], ![1559191301839, 74096445310, 82930788092], ![862828282323, 41003633459, 45892399064]]]
  hmulB := by decide  
  f := ![![![1219612, -219901, -22074]], ![![630156, -75991, -79403]], ![![-207351, 3766, 64507]]]
  g := ![![![-4602919739, 14102023123, 15783373769], ![-24185181639, 74096445310, 82930788092], ![-13383642345, 41003633459, 45892399064]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25409568729528831959911200336, 1207522590395152320824058461, 1351492634247170432358718289]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![25409568729528831959911200336, 1207522590395152320824058461, 1351492634247170432358718289]] 
 ![![23, 0, 0], ![18, 1, 0], ![4, 0, 1]] where
  M :=![![![25409568729528831959911200336, 1207522590395152320824058461, 1351492634247170432358718289], ![133509830702765836580443790955, 6344701806216427795354484462, 7101165498518895813409690938], ![73881926972420321284454685469, 3511043292027442105378615709, 3929656625426123153706367540]]]
  hmulB := by decide  
  f := ![![![-267028570581562, 62531408245961, -21161831799100]], ![![-292789092977778, 53847637525139, 3389944223349]], ![![246722214569703, -44627599977877, -4207818653801]]]
  g := ![![![-75296018894460501928553266, 1207522590395152320824058461, 1351492634247170432358718289], ![-395628861008932477807638831, 6344701806216427795354484462, 7101165498518895813409690938], ![-218933860251223009877646411, 3511043292027442105378615709, 3929656625426123153706367540]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![296745028722, 14102023123, 15783373769]] ![![296745028722, 14102023123, 15783373769]]
  ![![123663705141302819961868, 5876790714537139378907, 6577466481277181196750]] where
 M := ![![![123663705141302819961868, 5876790714537139378907, 6577466481277181196750]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![123663705141302819961868, 5876790714537139378907, 6577466481277181196750]] ![![25409568729528831959911200336, 1207522590395152320824058461, 1351492634247170432358718289]]
  ![![23, 0, 0]] where
 M := ![![![4412806646742824885684573131398759958730849128199583, 209706971798991606914299488767787780381391854553932, 234709834822941169415453262465534103471777033943618]]]
 hmul := by decide  
 g := ![![![![191861158554035864594981440495598259075254309921721, 9117694426043113344099977772512512190495298024084, 10204775427084398670237098368066700150946827562766]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23174919100733, -1101326773492, -1232635342902]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-23174919100733, -1101326773492, -1232635342902]] 
 ![![29, 0, 0], ![16, 1, 0], ![7, 0, 1]] where
  M :=![![![-23174919100733, -1101326773492, -1232635342902], ![-121768281808478, -5786715730695, -6476652071542], ![-67384366055860, -3202263884052, -3584062183711]]]
  hmulB := by decide  
  f := ![![![5139039, -210092, -1387774]], ![![-1821022, 771865, -768526]], ![![2069073, -707712, 567287]]]
  g := ![![![106026092257, -1101326773492, -1232635342902], ![557094289084, -5786715730695, -6476652071542], ![308285909481, -3202263884052, -3584062183711]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5252885162292003547704781, 249629482725058342902444, 279392211688101954232438]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![5252885162292003547704781, 249629482725058342902444, 279392211688101954232438]] 
 ![![29, 0, 0], ![26, 1, 0], ![16, 0, 1]] where
  M :=![![![5252885162292003547704781, 249629482725058342902444, 279392211688101954232438], ![27600303499196006246351374, 1311631469695532577120655, 1468014167387306446084670], ![15273509050311396726099052, 725833146133756124182348, 812372504245415891315767]]]
  hmulB := by decide  
  f := ![![![5758535462225, -1000191430124, -173066873410]], ![![4514967325408, -643125174137, -390621098142]], ![![22625469748, -129974531196, 227091724791]]]
  g := ![![![-196819199157556711568199, 249629482725058342902444, 279392211688101954232438], ![-1034149703140853237797944, 1311631469695532577120655, 1468014167387306446084670], ![-572279752313548853920492, 725833146133756124182348, 812372504245415891315767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-23174919100733, -1101326773492, -1232635342902]] ![![-23174919100733, -1101326773492, -1232635342902]]
  ![![754243895402813796218908185, 35843447484731249948105480, 40116976400240459151581152]] where
 M := ![![![754243895402813796218908185, 35843447484731249948105480, 40116976400240459151581152]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![754243895402813796218908185, 35843447484731249948105480, 40116976400240459151581152]] ![![5252885162292003547704781, 249629482725058342902444, 279392211688101954232438]]
  ![![29, 0, 0]] where
 M := ![![![5563973598067040073254461774372349513182374987729909, 264413138355250286978899355402862853524363642698436, 295938487385447561436875852673934304377457999320214]]]
 hmul := by decide  
 g := ![![![![191861158554035864594981440495598259075254309921721, 9117694426043113344099977772512512190495298024084, 10204775427084398670237098368066700150946827562766]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [28, 26, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 9, 23], [13, 21, 8], [0, 1]]
 g := ![![[29, 4, 18], [7, 16, 14], [10, 10, 18], [1]], ![[19, 21, 1, 12], [24, 29, 1, 11], [12, 13, 10, 13], [12, 14, 4, 15]], ![[13, 17, 16, 7], [9, 6, 7, 9], [30, 9, 11, 25], [6, 8, 21, 16]]]
 h' := ![![[25, 9, 23], [21, 22, 24], [30, 27, 18], [3, 5, 7], [0, 1]], ![[13, 21, 8], [11, 6, 18], [6, 6, 7], [6, 20, 14], [25, 9, 23]], ![[0, 1], [20, 3, 20], [3, 29, 6], [14, 6, 10], [13, 21, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 8], []]
 b := ![[], [23, 5, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [28, 26, 24, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24569112, -4694268, 54064]
  a := ![6, -6, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![792552, -151428, 1744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB166I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB166I0 : PrimesBelowBoundCertificateInterval O 1 31 166 where
  m := 11
  g := ![2, 3, 1, 2, 2, 2, 2, 3, 3, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB166I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1]
    · exact ![I29N0, I29N0, I29N1]
    · exact ![I31N0]
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
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
    · exact ![29, 29, 29]
    · exact ![29791]
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
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I5N0, I7N0, I7N1, I11N0, I11N1, I13N1, I17N1, I19N0, I19N1, I23N0, I23N1, I29N0, I29N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N0], [I5N0], [I7N0, I7N1], [I11N0, I11N1], [I13N1], [I17N1], [I19N0, I19N0, I19N1], [I23N0, I23N0, I23N1], [I29N0, I29N0, I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
