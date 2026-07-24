
import IdealArithmetic.Examples.NF3_1_196911_1.RI3_1_196911_1
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
  c := ![-189198, -5174, -6500]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94599, -2587, -3250]
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


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23767083794, -144925223, -2309107560]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![23767083794, -144925223, -2309107560]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![23767083794, -144925223, -2309107560], ![-196563993046, 23622158571, 1584481445], ![66191013085, -39254828520, 23912009017]]]
  hmulB := by decide  
  f := ![![![-627051816167352646107, -94109074541202346991, -54316473613058909525]], ![![-2019740679509039098607, -303126346596986562360, -174953948773023548160]], ![![-2259854349775183072164, -339163041987734602972, -195753071746403069547]]]
  g := ![![![8788680600, -144925223, -2309107560], ![-81797597211, 23622158571, 1584481445], ![40262887036, -39254828520, 23912009017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![23767083794, -144925223, -2309107560]] ![![23767083794, -144925223, -2309107560]]
  ![![440519183878347011094, 83775724784486938805, -110325784990577738395]] where
 M := ![![![440519183878347011094, 83775724784486938805, -110325784990577738395]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![440519183878347011094, 83775724784486938805, -110325784990577738395]] ![![23767083794, -144925223, -2309107560]]
  ![![3, 0, 0]] where
 M := ![![![-13300010105784560856876453837969, 6245940885439776760301046849093, -3522576261858373165779893405130]]]
 hmul := by decide  
 g := ![![![![-4433336701928186952292151279323, 2081980295146592253433682283031, -1174192087286124388593297801710]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189965640, -28510388, -16455201]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-189965640, -28510388, -16455201]] 
 ![![5, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-189965640, -28510388, -16455201], ![-1455712861, -218476028, -126096739], ![-1863906146, -279738417, -161455252]]]
  hmulB := by decide  
  f := ![![![23107, 959, -3104]], ![![-47763, 5005, 959]], ![![46653, -10170, 3188]]]
  g := ![![![-25708970, -28510388, -16455201], ![-197008671, -218476028, -126096739], ![-252251445, -279738417, -161455252]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-669195, -100434, -57967]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-669195, -100434, -57967]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![-669195, -100434, -57967], ![-5128063, -769629, -444203], ![-6566012, -985439, -568761]]]
  hmulB := by decide  
  f := ![![![448, -239, 141]], ![![2391, -6, -239]], ![![-4753, 336, 222]]]
  g := ![![![-78972, -100434, -57967], ![-605165, -769629, -444203], ![-774858, -985439, -568761]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19865097, -2552486, -31117]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![19865097, -2552486, -31117]] 
 ![![5, 0, 0], ![3, 1, 0], ![0, 0, 1]] where
  M :=![![![19865097, -2552486, -31117], ![-7749917, 17312611, -12731313], ![-215903332, -528989, 22417583]]]
  hmulB := by decide  
  f := ![![![381372169506656, 57237027312051, 33035214710605]], ![![813316762709099, 122064055750972, 70451113196293]], ![![748390004272753, 112319730016057, 64827028438921]]]
  g := ![![![5504511, -2552486, -31117], ![-11937550, 17312611, -12731313], ![-42863273, -528989, 22417583]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-189965640, -28510388, -16455201]] ![![-669195, -100434, -57967]]
  ![![381372169506656, 57237027312051, 33035214710605]] where
 M := ![![![381372169506656, 57237027312051, 33035214710605]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![381372169506656, 57237027312051, 33035214710605]] ![![19865097, -2552486, -31117]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 8, -9]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![27, 8, -9]] 
 ![![7, 0, 0], ![0, 7, 0], ![4, 3, 1]] where
  M :=![![![27, 8, -9], ![-749, 35, 49], ![986, -153, 19]]]
  hmulB := by decide  
  f := ![![![-1166, -175, -101]], ![![-8935, -1341, -774]], ![![-6130, -920, -531]]]
  g := ![![![9, 5, -9], ![-135, -16, 49], ![130, -30, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[2, 2], [4, 1]], ![[3, 5], [1, 6]]]
 h' := ![![[4, 6], [1, 4], [0, 1]], ![[0, 1], [3, 3], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5701, 2873, 169]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-911, 338, 169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1166, -175, -101]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1166, -175, -101]] 
 ![![7, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![-1166, -175, -101], ![-8935, -1341, -774], ![-11441, -1717, -991]]]
  hmulB := by decide  
  f := ![![![27, 8, -9]], ![![-107, 5, 7]], ![![164, -15, -5]]]
  g := ![![![-80, -175, -101], ![-613, -1341, -774], ![-785, -1717, -991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![27, 8, -9]] ![![-1166, -175, -101]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37307158, 8056997, -2490252]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-37307158, 8056997, -2490252]] 
 ![![11, 0, 0], ![2, 1, 0], ![8, 0, 1]] where
  M :=![![![-37307158, 8056997, -2490252], ![-195557426, -29250161, 42775237], ![769513313, -42334284, -45364155]]]
  hmulB := by decide  
  f := ![![![-3137767868704263, -470921896142103, -271799684252717]], ![![-2756395699197607, -413684868830052, -238764469542112]], ![![-5080846805192771, -762542709221183, -440113040598536]]]
  g := ![![![-3045376, 8056997, -2490252], ![-43569000, -29250161, 42775237], ![110645011, -42334284, -45364155]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32340727, 4853755, 2801418]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![32340727, 4853755, 2801418]] 
 ![![11, 0, 0], ![10, 1, 0], ![7, 0, 1]] where
  M :=![![![32340727, 4853755, 2801418], ![247828040, 37194482, 21467357], ![317320963, 47624106, 27486972]]]
  hmulB := by decide  
  f := ![![![-19338, 2448, 59]], ![![-16679, 690, 1161]], ![![6428, 1649, -1943]]]
  g := ![![![-3255159, 4853755, 2801418], ![-24944389, 37194482, 21467357], ![-31938991, 47624106, 27486972]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-37307158, 8056997, -2490252]] ![![32340727, 4853755, 2801418]]
  ![![19338, -2448, -59]] where
 M := ![![![19338, -2448, -59]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![19338, -2448, -59]] ![![32340727, 4853755, 2801418]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63552, 9538, 5505]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![63552, 9538, 5505]] 
 ![![13, 0, 0], ![2, 1, 0], ![7, 0, 1]] where
  M :=![![![63552, 9538, 5505], ![487001, 73090, 42185], ![623560, 93585, 54014]]]
  hmulB := by decide  
  f := ![![![35, -107, 80]], ![![512, -22, -35]], ![![-890, 47, 54]]]
  g := ![![![457, 9538, 5505], ![3502, 73090, 42185], ![4484, 93585, 54014]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14354334740559, 2154324608045, 1243400982289]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![14354334740559, 2154324608045, 1243400982289]] 
 ![![13, 0, 0], ![12, 1, 0], ![3, 0, 1]] where
  M :=![![![14354334740559, 2154324608045, 1243400982289], ![109997732710655, 16508659348604, 9528222057936], ![140841958285999, 21137816698913, 12200010132514]]]
  hmulB := by decide  
  f := ![![![6686888, -1923273, 820564]], ![![11241850, -1408897, -45397]], ![![-13178209, 629213, 851681]]]
  g := ![![![-1171366423296, 2154324608045, 1243400982289], ![-8976218895877, 16508659348604, 9528222057936], ![-11493220961423, 21137816698913, 12200010132514]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![63552, 9538, 5505]] ![![14354334740559, 2154324608045, 1243400982289]]
  ![![2736740036390657453, 410734911284976857, 237061856994513666]] where
 M := ![![![2736740036390657453, 410734911284976857, 237061856994513666]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![2736740036390657453, 410734911284976857, 237061856994513666]] ![![14354334740559, 2154324608045, 1243400982289]]
  ![![13, 0, 0]] where
 M := ![![![117852247740723348506865689009896, 17687479218655086461626904112071, 10208595748553331249875035973393]]]
 hmul := by decide  
 g := ![![![![9065557518517180654374283769992, 1360575324511929727817454162467, 785276596042563942298079690261]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2423036, -2952025, 2552486]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-2423036, -2952025, 2552486]] 
 ![![17, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-2423036, -2952025, 2552486], ![211057260, -5375061, -17312611], ![-337706649, 43392262, 528989]]]
  hmulB := by decide  
  f := ![![![-748390004272753, -112319730016057, -64827028438921]], ![![-381372169506656, -57237027312051, -33035214710605]], ![![-431944593202443, -64827028438921, -37415898485688]]]
  g := ![![![31117, -2952025, 2552486], ![12731313, -5375061, -17312611], ![-22417583, 43392262, 528989]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -3, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![23, -3, 0]] 
 ![![17, 0, 0], ![15, 1, 0], ![0, 0, 1]] where
  M :=![![![23, -3, 0], ![-6, 20, -15], ![-255, 0, 26]]]
  hmulB := by decide  
  f := ![![![520, 78, 45]], ![![693, 104, 60]], ![![300, 45, 26]]]
  g := ![![![4, -3, 0], ![-18, 20, -15], ![-15, 0, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-2423036, -2952025, 2552486]] ![![-2423036, -2952025, 2552486]]
  ![![-1479166698173618, 133778318559757, 46272732036433]] where
 M := ![![![-1479166698173618, 133778318559757, 46272732036433]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-1479166698173618, 133778318559757, 46272732036433]] ![![23, -3, 0]]
  ![![17, 0, 0]] where
 M := ![![![-46623050638642171, 7113066465715994, -803583745449097]]]
 hmul := by decide  
 g := ![![![![-2742532390508363, 418415674453882, -47269632085241]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [4, 1, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 16, 13], [18, 2, 6], [0, 1]]
 g := ![![[16, 18, 9], [4, 7, 17], [11, 1], []], ![[15, 9, 17, 15], [1, 6, 3, 10], [17, 4], [14, 17]], ![[14, 10, 3, 17], [3, 4, 12, 7], [11, 9], [2, 17]]]
 h' := ![![[12, 16, 13], [3, 4, 16], [13, 4, 6], [0, 0, 1], [0, 1]], ![[18, 2, 6], [15, 13, 8], [0, 14, 7], [12, 17, 2], [12, 16, 13]], ![[0, 1], [1, 2, 14], [5, 1, 6], [12, 2, 16], [18, 2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 4], []]
 b := ![[], [3, 0, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [4, 1, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3650529755, -140647918, -172588666]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-192133145, -7402522, -9083614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9535, 348, 700]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-9535, 348, 700]] 
 ![![23, 0, 0], ![0, 23, 0], ![1, 21, 1]] where
  M :=![![![-9535, 348, 700], ![60196, -9187, 1040], ![5780, 11900, -9883]]]
  hmulB := by decide  
  f := ![![![3409527, 511708, 295340]], ![![26127316, 3921235, 2263200]], ![![25458121, 3820801, 2205233]]]
  g := ![![![-445, -624, 700], ![2572, -1349, 1040], ![681, 9541, -9883]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [13, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 22], [0, 1]]
 g := ![![[11, 16], [2, 9], [5, 2], [1]], ![[0, 7], [3, 14], [18, 21], [1]]]
 h' := ![![[18, 22], [20, 4], [4, 3], [10, 18], [0, 1]], ![[0, 1], [0, 19], [12, 20], [12, 5], [18, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [7, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [13, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3521, 2879, 44]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-155, 85, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3409527, 511708, 295340]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![3409527, 511708, 295340]] 
 ![![23, 0, 0], ![11, 1, 0], ![20, 0, 1]] where
  M :=![![![3409527, 511708, 295340], ![26127316, 3921235, 2263200], ![33453620, 5020780, 2897819]]]
  hmulB := by decide  
  f := ![![![-9535, 348, 700]], ![![-1943, -233, 380]], ![![-8040, 820, 179]]]
  g := ![![![-353307, 511708, 295340], ![-2707403, 3921235, 2263200], ![-3466580, 5020780, 2897819]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-9535, 348, 700]] ![![3409527, 511708, 295340]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [22, 1, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 24, 10], [13, 4, 19], [0, 1]]
 g := ![![[18, 12, 4], [11, 5], [3, 28, 7], [1]], ![[21, 7, 16, 21], [14, 4], [16, 3, 8, 18], [27, 16, 11, 14]], ![[22, 25, 11, 21], [17, 24], [24, 7, 28, 8], [12, 22, 8, 15]]]
 h' := ![![[10, 24, 10], [25, 9, 2], [21, 10, 18], [7, 28, 23], [0, 1]], ![[13, 4, 19], [27, 3, 11], [25, 5, 27], [0, 6, 24], [10, 24, 10]], ![[0, 1], [8, 17, 16], [18, 14, 13], [19, 24, 11], [13, 4, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 18], []]
 b := ![[], [23, 2, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [22, 1, 6, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-184005, -2552, -6380]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6345, -88, -220]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [6, 19, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 6, 25], [0, 24, 6], [0, 1]]
 g := ![![[14, 22, 1], [26, 7, 7], [27, 15, 19], [1]], ![[3, 27, 21, 14], [6, 5, 1, 14], [14, 21, 27, 18], [19, 18, 6, 1]], ![[0, 30, 23, 29], [3, 19, 14, 30], [9, 24, 3, 24], [22, 30, 10, 30]]]
 h' := ![![[9, 6, 25], [30, 9, 30], [24, 22, 10], [25, 12, 9], [0, 1]], ![[0, 24, 6], [23, 21, 15], [17, 28, 15], [26, 28, 20], [9, 6, 25]], ![[0, 1], [13, 1, 17], [8, 12, 6], [23, 22, 2], [0, 24, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 20], []]
 b := ![[], [2, 30, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [6, 19, 22, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4518529, 805721, 314650]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![145759, 25991, 10150]
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



lemma PB126I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB126I0 : PrimesBelowBoundCertificateInterval O 1 31 126 where
  m := 11
  g := ![1, 3, 3, 2, 3, 3, 3, 1, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB126I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N1]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0, I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
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
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![29791]
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
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I3N0, I5N0, I5N1, I5N2, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I17N0, I17N1, I23N1]
  Il := ![[I2N0], [I3N0, I3N0, I3N0], [I5N0, I5N1, I5N2], [I7N0, I7N1], [I11N0, I11N1, I11N1], [I13N0, I13N1, I13N1], [I17N0, I17N0, I17N1], [], [I23N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
