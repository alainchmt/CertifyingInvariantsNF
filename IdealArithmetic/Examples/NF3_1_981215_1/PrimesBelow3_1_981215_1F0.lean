
import IdealArithmetic.Examples.NF3_1_981215_1.RI3_1_981215_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 1]], ![[0, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 1, 1], [0, 0, 1]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3417850, 281854, -200332]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1708925, 140927, -100166]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀

instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 2], [1, 0, 1], [0, 1]]
 g := ![![[1]], ![[0, 0, 1, 2]], ![[2, 0, 2, 1]]]
 h' := ![![[1, 2, 2], [0, 1]], ![[1, 0, 1], [1, 2, 2]], ![[0, 1], [1, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [0, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 1, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112227261, -9310884, 1924392]
  a := ![-3, 6, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37409087, -3103628, 641464]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51474124348028782, 3325373074251827, 2889764139173906]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![51474124348028782, 3325373074251827, 2889764139173906]] 
 ![![5, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![51474124348028782, 3325373074251827, 2889764139173906], ![548619577507964219, 35442366318219109, 30799575538422285], ![386626541213143041, 24977160976037771, 21705265086133880]]]
  hmulB := by decide  
  f := ![![![-359813815, 37004766, -4605059]], ![![-255276970, -34069844, 82331497]], ![![1492789076, -84107803, -79396575]]]
  g := ![![![9629750254755391, 3325373074251827, 2889764139173906], ![102635442237949022, 35442366318219109, 30799575538422285], ![72329876047421054, 24977160976037771, 21705265086133880]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6040998079, 390265451, 339142430]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![6040998079, 390265451, 339142430]] 
 ![![5, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![6040998079, 390265451, 339142430], ![64385938679, 4159512562, 3614635101], ![45374452161, 2931317111, 2547327737]]]
  hmulB := by decide  
  f := ![![![18983, 5343, -10109]], ![![-372046, 29473, 7711]], ![![381774, -46963, 15812]]]
  g := ![![![828158769, 390265451, 339142430], ![8826650666, 4159512562, 3614635101], ![6220371196, 2931317111, 2547327737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![51474124348028782, 3325373074251827, 2889764139173906]] ![![6040998079, 390265451, 339142430]]
  ![![656183817837744590380937177, 42391318497115222788667022, 36838246196729199045430509]] where
 M := ![![![656183817837744590380937177, 42391318497115222788667022, 36838246196729199045430509]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![656183817837744590380937177, 42391318497115222788667022, 36838246196729199045430509]] ![![6040998079, 390265451, 339142430]]
  ![![5, 0, 0]] where
 M := ![![![8364925256054549413811155115388606870, 540397676831545940733911175821841690, 469608008644876345040715641289187465]]]
 hmul := by decide  
 g := ![![![![1672985051210909882762231023077721374, 108079535366309188146782235164368338, 93921601728975269008143128257837493]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, -13, 5]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![101, -13, 5]] 
 ![![7, 0, 0], ![0, 7, 0], ![2, 3, 1]] where
  M :=![![![101, -13, 5], ![968, 17, -153], ![-2913, 212, 87]]]
  hmulB := by decide  
  f := ![![![-4845, -313, -272]], ![![-51639, -3336, -2899]], ![![-28714, -1855, -1612]]]
  g := ![![![13, -4, 5], ![182, 68, -153], ![-441, -7, 87]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[6, 1], [5, 1]], ![[4, 6], [3, 6]]]
 h' := ![![[5, 6], [3, 6], [0, 1]], ![[0, 1], [5, 1], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [1, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1402802, 30579, -17184]
  a := ![1, -66, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![205310, 11733, -17184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4845, 313, 272]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![4845, 313, 272]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![4845, 313, 272], ![51639, 3336, 2899], ![36391, 2351, 2043]]]
  hmulB := by decide  
  f := ![![![-101, 13, -5]], ![![-196, 5, 19]], ![![344, -21, -16]]]
  g := ![![![319, 313, 272], ![3400, 3336, 2899], ![2396, 2351, 2043]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![101, -13, 5]] ![![4845, 313, 272]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-464350660, 108079376, -91541615]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-464350660, 108079376, -91541615]] 
 ![![11, 0, 0], ![2, 1, 0], ![0, 0, 11]] where
  M :=![![![-464350660, 108079376, -91541615], ![-17592527841, 683762003, 1371956366], ![28515739706, -2712005069, 51823508]]]
  hmulB := by decide  
  f := ![![![-341471596788307798, -22060024681606857, -19170260542432951]], ![![-392945721136336580, -25385397755858684, -22060024681606857]], ![![-2564822307537675901, -165694728171764356, -143989463085630476]]]
  g := ![![![-61864492, 108079376, -8321965], ![-1723641077, 683762003, 124723306], ![3085431804, -2712005069, 4711228]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 7, 1] where
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
 g := ![![[9, 1], [4, 5], [1]], ![[2, 10], [2, 6], [1]]]
 h' := ![![[4, 10], [3, 10], [9, 4], [0, 1]], ![[0, 1], [10, 1], [3, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [6, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2513, 15480, -8965]
  a := ![3, -7, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3043, 15480, -815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-341471596788307798, -22060024681606857, -19170260542432951]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-341471596788307798, -22060024681606857, -19170260542432951]] 
 ![![11, 0, 0], ![6, 1, 0], ![9, 0, 1]] where
  M :=![![![-341471596788307798, -22060024681606857, -19170260542432951], ![-3639459738923086784, -235119325951231810, -204319750412809525], ![-2564822307537675901, -165694728171764356, -143989463085630476]]]
  hmulB := by decide  
  f := ![![![-464350660, 108079376, -91541615]], ![![-1852602891, 121112569, 74791516]], ![![2212416706, -158117335, -70186457]]]
  g := ![![![-3325373074251827, -22060024681606857, -19170260542432951], ![-35442366318219109, -235119325951231810, -204319750412809525], ![-24977160976037771, -165694728171764356, -143989463085630476]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-464350660, 108079376, -91541615]] ![![-341471596788307798, -22060024681606857, -19170260542432951]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [1, 11, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 3, 9], [6, 9, 4], [0, 1]]
 g := ![![[2, 2, 9], [2, 3], [1]], ![[1, 1, 12, 10], [1, 4], [11, 0, 5, 1]], ![[7, 12, 0, 9], [6, 10], [7, 6, 12, 12]]]
 h' := ![![[11, 3, 9], [12, 10, 10], [12, 2, 4], [0, 1]], ![[6, 9, 4], [9, 4, 11], [7, 6, 2], [11, 3, 9]], ![[0, 1], [8, 12, 5], [1, 5, 7], [6, 9, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 1], []]
 b := ![[], [12, 7, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [1, 11, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3360357, 295737, -209352]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-258489, 22749, -16104]
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

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [9, 1, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 13, 14], [8, 3, 3], [0, 1]]
 g := ![![[10, 13, 8], [0, 13], [3, 1], []], ![[8, 4, 2, 7], [14, 13], [2, 9], [0, 9]], ![[4, 13, 8, 5], [], [9, 16], [11, 9]]]
 h' := ![![[12, 13, 14], [15, 4, 5], [7, 5, 8], [0, 0, 1], [0, 1]], ![[8, 3, 3], [1, 0, 3], [12, 9, 9], [8, 10, 3], [12, 13, 14]], ![[0, 1], [8, 13, 9], [5, 3], [16, 7, 13], [8, 3, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 6], []]
 b := ![[], [9, 10, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [9, 1, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11529468, 2220268, 495482]
  a := ![-1, 23, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![678204, 130604, 29146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2212416706, -158117335, -70186457]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![2212416706, -158117335, -70186457]] 
 ![![19, 0, 0], ![0, 19, 0], ![9, 0, 1]] where
  M :=![![![2212416706, -158117335, -70186457], ![-13247495952, 2369742814, -1598917771], ![-24164375683, 89513332, 3090143032]]]
  hmulB := by decide  
  f := ![![![-392945721136336580, -25385397755858684, -22060024681606857]], ![![-4188079316431051003, -270561692269450919, -235119325951231810]], ![![-341471596788307798, -22060024681606857, -19170260542432951]]]
  g := ![![![149689201, -8321965, -70186457], ![60145473, 124723306, -1598917771], ![-2735561209, 4711228, 3090143032]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 18], [0, 1]]
 g := ![![[10, 11], [13, 1], [17], [1]], ![[0, 8], [0, 18], [17], [1]]]
 h' := ![![[6, 18], [4, 12], [6, 18], [12, 6], [0, 1]], ![[0, 1], [0, 7], [0, 1], [10, 13], [6, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [15, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [7, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7780, 2508, -1369]
  a := ![1, -1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![239, 132, -1369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-392945721136336580, -25385397755858684, -22060024681606857]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-392945721136336580, -25385397755858684, -22060024681606857]] 
 ![![19, 0, 0], ![2, 1, 0], ![18, 0, 1]] where
  M :=![![![-392945721136336580, -25385397755858684, -22060024681606857], ![-4188079316431051003, -270561692269450919, -235119325951231810], ![-2951448848750818942, -190671889147802127, -165694728171764356]]]
  hmulB := by decide  
  f := ![![![2212416706, -158117335, -70186457]], ![![-464350660, 108079376, -91541615]], ![![824164475, -145084142, 96146674]]]
  g := ![![![2889764139173906, -25385397755858684, -22060024681606857], ![30799575538422285, -270561692269450919, -235119325951231810], ![21705265086133880, -190671889147802127, -165694728171764356]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![2212416706, -158117335, -70186457]] ![![-392945721136336580, -25385397755858684, -22060024681606857]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4971, 1465, -1417]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-4971, 1465, -1417]] 
 ![![23, 0, 0], ![0, 23, 0], ![15, 12, 1]] where
  M :=![![![-4971, 1465, -1417], ![-272112, 12177, 18949], ![401677, -40108, 3435]]]
  hmulB := by decide  
  f := ![![![34862369, 2252207, 1957178]], ![![371568791, 24004388, 20859921]], ![![227983272, 14728360, 12799011]]]
  g := ![![![708, 803, -1417], ![-24189, -9357, 18949], ![15224, -3536, 3435]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [11, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22], [0, 1]]
 g := ![![[3, 3], [15, 8], [2, 8], [1]], ![[19, 20], [4, 15], [14, 15], [1]]]
 h' := ![![[13, 22], [19, 16], [1, 13], [12, 13], [0, 1]], ![[0, 1], [20, 7], [9, 10], [20, 10], [13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [22, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [11, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17150, 6613, -3817]
  a := ![-2, 7, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3235, 2279, -3817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34862369, -2252207, -1957178]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-34862369, -2252207, -1957178]] 
 ![![23, 0, 0], ![8, 1, 0], ![17, 0, 1]] where
  M :=![![![-34862369, -2252207, -1957178], ![-371568791, -24004388, -20859921], ![-261854229, -16916519, -14700531]]]
  hmulB := by decide  
  f := ![![![4971, -1465, 1417]], ![![13560, -1039, -331]], ![![-13790, 661, 898]]]
  g := ![![![714231, -2252207, -1957178], ![7612390, -24004388, -20859921], ![5364650, -16916519, -14700531]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-4971, 1465, -1417]] ![![-34862369, -2252207, -1957178]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![428995, -13444, -38038]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![428995, -13444, -38038]] 
 ![![29, 0, 0], ![18, 1, 0], ![13, 0, 1]] where
  M :=![![![428995, -13444, -38038], ![-7251814, 731005, -71808], ![703464, -601726, 760187]]]
  hmulB := by decide  
  f := ![![![512491757327, 33108407616, 28771354942]], ![![506450759248, 32718142165, 28432212512]], ![![362474557755, 23416874978, 20349369545]]]
  g := ![![![40189, -13444, -38038], ![-671600, 731005, -71808], ![56969, -601726, 760187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18005002, -312689, -1953421]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![18005002, -312689, -1953421]] 
 ![![29, 0, 0], ![21, 1, 0], ![20, 0, 1]] where
  M :=![![![18005002, -312689, -1953421], ![-372790722, 34647724, 467263], ![108270607, -34300798, 34257748]]]
  hmulB := by decide  
  f := ![![![-1202980491341426, -77715920094330, -67535483663597]], ![![-1313246613028367, -84839421401137, -73725838298137]], ![![-1141217205854352, -73725838298137, -64068084659170]]]
  g := ![![![2194479, -312689, -1953421], ![-38266834, 34647724, 467263], ![4945945, -34300798, 34257748]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![428995, -13444, -38038]] ![![428995, -13444, -38038]]
  ![![254771733809, 7293413588, -44268718164]] where
 M := ![![![254771733809, 7293413588, -44268718164]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![254771733809, 7293413588, -44268718164]] ![![18005002, -312689, -1953421]]
  ![![29, 0, 0]] where
 M := ![![![-2924752327268823466, 1691488221804166183, -2010815103860875617]]]
 hmul := by decide  
 g := ![![![![-100853528526511154, 58327180062212627, -69338451857271573]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1251483327541293, -80849339604944, -70258439293710]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-1251483327541293, -80849339604944, -70258439293710]] 
 ![![31, 0, 0], ![14, 1, 0], ![29, 0, 1]] where
  M :=![![![-1251483327541293, -80849339604944, -70258439293710], ![-13338512565493666, -861705392712735, -748825857066964], ![-9399998085285244, -607266290135994, -527717133981725]]]
  hmulB := by decide  
  f := ![![![-140065659, 6850660, 8926834]], ![![-8475632, -3353095, 5886428]], ![![-113585025, 9891066, 1086985]]]
  g := ![![![61867811820823, -80849339604944, -70258439293710], ![659397186691180, -861705392712735, -748825857066964], ![464694414906087, -607266290135994, -527717133981725]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![110266121686941, 7123501306807, 6190354634540]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![110266121686941, 7123501306807, 6190354634540]] 
 ![![31, 0, 0], ![23, 1, 0], ![16, 0, 1]] where
  M :=![![![110266121686941, 7123501306807, 6190354634540], ![1175234233890333, 75923433896502, 65977805105797], ![828218251029697, 53505226294997, 46496281997007]]]
  hmulB := by decide  
  f := ![![![-5028095, 2669731, -3118901]], ![![-23033097, 2982420, -1165480]], ![![22506277, -1308742, -1139315]]]
  g := ![![![-4923228468460, 7123501306807, 6190354634540], ![-52472568626515, 75923433896502, 65977805105797], ![-36978789216366, 53505226294997, 46496281997007]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84397753, -5452332, -4738101]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-84397753, -5452332, -4738101]] 
 ![![31, 0, 0], ![24, 1, 0], ![3, 0, 1]] where
  M :=![![![-84397753, -5452332, -4738101], ![-899524959, -58111840, -50499450], ![-633918726, -40952931, -35588281]]]
  hmulB := by decide  
  f := ![![![40910, -2739, -1560]], ![![22149, -613, -2079]], ![![-8589, -426, 1748]]]
  g := ![![![1957178, -5452332, -4738101], ![20859921, -58111840, -50499450], ![14700531, -40952931, -35588281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-1251483327541293, -80849339604944, -70258439293710]] ![![110266121686941, 7123501306807, 6190354634540]]
  ![![-291202446286914411238352266935, -18812496303802643151804556209, -16348143794152111273292246558]] where
 M := ![![![-291202446286914411238352266935, -18812496303802643151804556209, -16348143794152111273292246558]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-291202446286914411238352266935, -18812496303802643151804556209, -16348143794152111273292246558]] ![![-84397753, -5452332, -4738101]]
  ![![31, 0, 0]] where
 M := ![![![51862536587538206365629161715409362594, 3350465596355584832550249290095418478, 2911569653598233339252436975992962283]]]
 hmul := by decide  
 g := ![![![![1672985051210909882762231023077721374, 108079535366309188146782235164368338, 93921601728975269008143128257837493]]]]
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


lemma PB281I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB281I0 : PrimesBelowBoundCertificateInterval O 1 31 281 where
  m := 11
  g := ![1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB281I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N0, I29N1]
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
    · exact ![8]
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![29, 29, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I3N0, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I19N1, I23N1, I29N0, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0], [I3N0], [I5N0, I5N1, I5N1], [I7N0, I7N1], [I11N0, I11N1], [], [], [I19N1], [I23N1], [I29N0, I29N0, I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
