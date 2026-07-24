
import IdealArithmetic.Examples.NF3_1_132020_1.RI3_1_132020_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31538261021712216828968174, 8270232720260206534071181, -1718144617341998104945344]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-31538261021712216828968174, 8270232720260206534071181, -1718144617341998104945344]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-31538261021712216828968174, 8270232720260206534071181, -1718144617341998104945344], ![120270123213939867346174080, -31538261021712216828968174, 6552088102918208429125837], ![-458646167204274590038808590, 120270123213939867346174080, -24986172918794008399842337]]]
  hmulB := by decide  
  f := ![![![-2195163077678, 1306774093523, 493621278359]], ![![-17276744742565, -1097581538839, 900197685941]], ![![-63013838015870, -17276744742565, -197383852898]]]
  g := ![![![-15769130510856108414484087, 8270232720260206534071181, -1718144617341998104945344], ![60135061606969933673087040, -31538261021712216828968174, 6552088102918208429125837], ![-229323083602137295019404295, 120270123213939867346174080, -24986172918794008399842337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1083, -284, 59]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1083, -284, 59]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![1083, -284, 59], ![-4130, 1083, -225], ![15750, -4130, 858]]]
  hmulB := by decide  
  f := ![![![-36, 2, 3]], ![![-123, -17, 4]], ![![-193, -104, -14]]]
  g := ![![![654, -284, 59], ![-2494, 1083, -225], ![9511, -4130, 858]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-31538261021712216828968174, 8270232720260206534071181, -1718144617341998104945344]] ![![-31538261021712216828968174, 8270232720260206534071181, -1718144617341998104945344]]
  ![![2777344259993866692194571341257981190674969069787716, -728298981310832611930751923654413290288349308670508, 151304445337965909393157449734046244609788351914281]] where
 M := ![![![2777344259993866692194571341257981190674969069787716, -728298981310832611930751923654413290288349308670508, 151304445337965909393157449734046244609788351914281]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2777344259993866692194571341257981190674969069787716, -728298981310832611930751923654413290288349308670508, 151304445337965909393157449734046244609788351914281]] ![![1083, -284, 59]]
  ![![2, 0, 0]] where
 M := ![![![8398783640460059387862956040586348870996040690039220218, -2202400925843689065098002861636607241772399410515852038, 457549796234550222783227983828275558439900175510792642]]]
 hmul := by decide  
 g := ![![![![4199391820230029693931478020293174435498020345019610109, -1101200462921844532549001430818303620886199705257926019, 228774898117275111391613991914137779219950087755396321]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 1], [0, 1, 2], [0, 1]]
 g := ![![[1]], ![[2, 2, 1, 1]], ![[0, 1, 2, 2]]]
 h' := ![![[1, 1, 1], [0, 1]], ![[0, 1, 2], [1, 1, 1]], ![[0, 1], [0, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 2], []]
 b := ![[], [1, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4758, 348, 348]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1586, 116, 116]
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


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11621205, 2165109, -231365]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![11621205, 2165109, -231365]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![11621205, 2165109, -231365], ![16195550, 11621205, 1933744], ![-135362080, 16195550, 13554949]]]
  hmulB := by decide  
  f := ![![![-126206793454345, 33095025500191, -6875506632921]], ![![96257092860894, -25241358690869, 5243903773454]], ![![-367073264141780, 96257092860894, -19997454917415]]]
  g := ![![![2324241, 2165109, -231365], ![3239110, 11621205, 1933744], ![-27072416, 16195550, 13554949]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21667070897921, 1515966648207, 1887440242659]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-21667070897921, 1515966648207, 1887440242659]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![-21667070897921, 1515966648207, 1887440242659], ![-132120816986130, -21667070897921, 3403406890866], ![-238238482360620, -132120816986130, -18263664007055]]]
  hmulB := by decide  
  f := ![![![-845381001854109131674521235, 221683041363852541086219285, -46054752890112506322189201]], ![![-31538261021712216828968174, 8270232720260206534071181, -1718144617341998104945344]], ![![-3135100840115647792036038164, 822112973552657121379624242, -170794344988163824439849591]]]
  g := ![![![-7056139692277, 1515966648207, 1887440242659], ![-11813232191582, -21667070897921, 3403406890866], ![72659888322424, -132120816986130, -18263664007055]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![11621205, 2165109, -231365]] ![![11621205, 2165109, -231365]]
  ![![201435584356175, 46575267646940, -1638114332114]] where
 M := ![![![201435584356175, 46575267646940, -1638114332114]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![201435584356175, 46575267646940, -1638114332114]] ![![-21667070897921, 1515966648207, 1887440242659]]
  ![![5, 0, 0]] where
 M := ![![![-10127819628054751384253003695, -487350994674255776443304695, 568630184837771673792983635]]]
 hmul := by decide  
 g := ![![![![-2025563925610950276850600739, -97470198934851155288660939, 113726036967554334758596727]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-838061, -13638, 54052]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-838061, -13638, 54052]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-838061, -13638, 54052], ![-3783640, -838061, 40414], ![-2828980, -3783640, -797647]]]
  hmulB := by decide  
  f := ![![![-821388869427, 215391619066, -44747707040]], ![![447477070400, -117341267061, 24377701718]], ![![-1706439120260, 447477070400, -92963565343]]]
  g := ![![![-119723, -13638, 54052], ![-540520, -838061, 40414], ![-404140, -3783640, -797647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269124859211722737920847, -70572223844426026386052, 14661411671658520679548]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![269124859211722737920847, -70572223844426026386052, 14661411671658520679548]] 
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![269124859211722737920847, -70572223844426026386052, 14661411671658520679548], ![-1026298817016096447568360, 269124859211722737920847, -55910812172767505706504], ![3913756852093725399455280, -1026298817016096447568360, 213214047038955232214343]]]
  hmulB := by decide  
  f := ![![![601035495081, -181654357444, -88964454948]], ![![1404817830978, -69841521369, -114915077440]], ![![3221361405418, 733940814528, -29052863857]]]
  g := ![![![86369961749761110308553, -70572223844426026386052, 14661411671658520679548], ![-329369014178546834407774, 269124859211722737920847, -55910812172767505706504], ![1256037924565224670225626, -1026298817016096447568360, 213214047038955232214343]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-838061, -13638, 54052]] ![![-838061, -13638, 54052]]
  ![![601035495081, -181654357444, -88964454948]] where
 M := ![![![601035495081, -181654357444, -88964454948]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![601035495081, -181654357444, -88964454948]] ![![269124859211722737920847, -70572223844426026386052, 14661411671658520679548]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15989332129, 4192859513, -871068475]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-15989332129, 4192859513, -871068475]] 
 ![![11, 0, 0], ![0, 11, 0], ![6, 2, 1]] where
  M :=![![![-15989332129, 4192859513, -871068475], ![60974793250, -15989332129, 3321791038], ![-232525372660, 60974793250, -12667541091]]]
  hmulB := by decide  
  f := ![![![-101749, 4097, 8071]], ![![-564970, -101749, 12168]], ![![-235654, -67626, -1529]]]
  g := ![![![-978447389, 539545133, -871068475], ![3731277002, -2057537655, 3321791038], ![-14229102374, 7846352312, -12667541091]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 0, 1] where
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
 g := ![![[0, 1], [], [1]], ![[0, 10], [], [1]]]
 h' := ![![[0, 10], [0, 1], [10], [0, 1]], ![[0, 1], [0, 10], [10], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![212, -626, -5]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, -56, -5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101749, 4097, 8071]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-101749, 4097, 8071]] 
 ![![11, 0, 0], ![8, 1, 0], ![2, 0, 1]] where
  M :=![![![-101749, 4097, 8071], ![-564970, -101749, 12168], ![-851760, -564970, -89581]]]
  hmulB := by decide  
  f := ![![![-15989332129, 4192859513, -871068475]], ![![-6085442162, 1595776725, -331523342]], ![![-24045821538, 6305501116, -1309970731]]]
  g := ![![![-13697, 4097, 8071], ![20426, -101749, 12168], ![349742, -564970, -89581]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-15989332129, 4192859513, -871068475]] ![![-101749, 4097, 8071]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-349, 225, 83]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-349, 225, 83]] 
 ![![13, 0, 0], ![0, 13, 0], ![3, 6, 1]] where
  M :=![![![-349, 225, 83], ![-5810, -349, 308], ![-21560, -5810, -41]]]
  hmulB := by decide  
  f := ![![![138753, -36385, 7559]], ![![-529130, 138753, -28826]], ![![-56977, 14941, -3104]]]
  g := ![![![-46, -21, 83], ![-518, -169, 308], ![-1649, -428, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [8, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 12], [0, 1]]
 g := ![![[1, 10], [3], [5, 1]], ![[12, 3], [3], [10, 12]]]
 h' := ![![[5, 12], [3, 7], [12, 4], [0, 1]], ![[0, 1], [12, 6], [6, 9], [5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [8, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3662, -190, 120]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![254, -70, 120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-138753, 36385, -7559]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-138753, 36385, -7559]] 
 ![![13, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![-138753, 36385, -7559], ![529130, -138753, 28826], ![-2017820, 529130, -109927]]]
  hmulB := by decide  
  f := ![![![349, -225, -83]], ![![608, -77, -62]], ![![1739, 395, -16]]]
  g := ![![![-25722, 36385, -7559], ![98090, -138753, 28826], ![-374063, 529130, -109927]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-349, 225, 83]] ![![-138753, 36385, -7559]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3299, 237, 289]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-3299, 237, 289]] 
 ![![17, 0, 0], ![1, 1, 0], ![16, 0, 1]] where
  M :=![![![-3299, 237, 289], ![-20230, -3299, 526], ![-36820, -20230, -2773]]]
  hmulB := by decide  
  f := ![![![19789107, -5189269, 1078073]], ![![-3275059, 858814, -178419]], ![![35553496, -9323142, 1936887]]]
  g := ![![![-480, 237, 289], ![-1491, -3299, 526], ![1634, -20230, -2773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159, -15, 7]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-159, -15, 7]] 
 ![![17, 0, 0], ![3, 1, 0], ![8, 0, 1]] where
  M :=![![![-159, -15, 7], ![-490, -159, -8], ![560, -490, -167]]]
  hmulB := by decide  
  f := ![![![-22633, 5935, -1233]], ![![1083, -284, 59]], ![![-30012, 7870, -1635]]]
  g := ![![![-10, -15, 7], ![3, -159, -8], ![198, -490, -167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73565271373, -19290915056, 4007696396]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![73565271373, -19290915056, 4007696396]] 
 ![![17, 0, 0], ![12, 1, 0], ![9, 0, 1]] where
  M :=![![![73565271373, -19290915056, 4007696396], ![-280538747720, 73565271373, -15283218660], ![1069825306200, -280538747720, 58282052713]]]
  hmulB := by decide  
  f := ![![![-570251, 129808, 73252]], ![![-704156, 58085, 63652]], ![![-1138027, -232904, 17181]]]
  g := ![![![15822763793, -19290915056, 4007696396], ![-60339590368, 73565271373, -15283218660], ![230103047319, -280538747720, 58282052713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-3299, 237, 289]] ![![-159, -15, 7]]
  ![![570251, -129808, -73252]] where
 M := ![![![570251, -129808, -73252]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![570251, -129808, -73252]] ![![73565271373, -19290915056, 4007696396]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [13, 2, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 16, 8], [17, 2, 11], [0, 1]]
 g := ![![[10, 8, 17], [14, 12, 1], [1, 1], []], ![[17, 7, 6, 3], [13, 14, 15, 18], [10, 4], [16, 7]], ![[14, 8, 8, 7], [2, 14, 8, 17], [18, 9], [13, 7]]]
 h' := ![![[3, 16, 8], [8, 4, 6], [6, 4, 18], [0, 0, 1], [0, 1]], ![[17, 2, 11], [4, 16, 6], [8, 15, 11], [10, 11, 2], [3, 16, 8]], ![[0, 1], [17, 18, 7], [11, 0, 9], [6, 8, 16], [17, 2, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 13], []]
 b := ![[], [8, 13, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [13, 2, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-136116, -12559, 1843]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7164, -661, 97]
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


def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123646689, 32423693, -6736037]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-123646689, 32423693, -6736037]] 
 ![![23, 0, 0], ![7, 1, 0], ![20, 0, 1]] where
  M :=![![![-123646689, 32423693, -6736037], ![471522590, -123646689, 25687656], ![-1798135920, 471522590, -97959033]]]
  hmulB := by decide  
  f := ![![![57303, 6961, -2115]], ![![23877, 4610, -433]], ![![35080, 12490, 863]]]
  g := ![![![-9386600, 32423693, -6736037], ![35795491, -123646689, 25687656], ![-136504930, 471522590, -97959033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![218767833, 21071592, -9517738]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![218767833, 21071592, -9517738]] 
 ![![23, 0, 0], ![8, 1, 0], ![5, 0, 1]] where
  M :=![![![218767833, 21071592, -9517738], ![666241660, 218767833, 11553854], ![-808769780, 666241660, 230321687]]]
  hmulB := by decide  
  f := ![![![42689317489536631, -11194358181780784, 2325633014837322]], ![![7770444733812196, -2037632520204767, 423319084858918]], ![![36272058657988065, -9511569649892020, 1976032930294773]]]
  g := ![![![4251469, 21071592, -9517738], ![-49637838, 218767833, 11553854], ![-316970065, 666241660, 230321687]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-123646689, 32423693, -6736037]] ![![-123646689, 32423693, -6736037]]
  ![![42689317489536631, -11194358181780784, 2325633014837322]] where
 M := ![![![42689317489536631, -11194358181780784, 2325633014837322]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![42689317489536631, -11194358181780784, 2325633014837322]] ![![218767833, 21071592, -9517738]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![504343051488183746525569937, -132253151300318878518752844, 27475652465800311158445956]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![504343051488183746525569937, -132253151300318878518752844, 27475652465800311158445956]] 
 ![![29, 0, 0], ![0, 29, 0], ![6, 26, 1]] where
  M :=![![![504343051488183746525569937, -132253151300318878518752844, 27475652465800311158445956], ![-1923295672606021781091216920, 504343051488183746525569937, -104777498834518567360306888], ![7334424918416299715221482160, -1923295672606021781091216920, 399565552653665179165263049]]]
  hmulB := by decide  
  f := ![![![-19471907820243, 209192554684, 1393818964300]], ![![-97567327501000, -19471907820243, 1603011518984]], ![![-95372164423322, -20778681913766, 1109390240625]]]
  g := ![![![11706521954944202743961869, -29193797083142309263391300, 27475652465800311158445956], ![-44642437227548633687219848, 111329586937436775789432725, -104777498834518567360306888], ![170242469051527884145858754, -424551725572459187565105386, 399565552653665179165263049]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 28], [0, 1]]
 g := ![![[], [6], [0, 4], [0, 1]], ![[], [6], [0, 25], [0, 28]]]
 h' := ![![[0, 28], [17], [0, 21], [0, 27], [0, 1]], ![[0, 1], [17], [0, 8], [0, 2], [0, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [0, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-208, -70, 4]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -6, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19471907820243, 209192554684, 1393818964300]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-19471907820243, 209192554684, 1393818964300]] 
 ![![29, 0, 0], ![2, 1, 0], ![25, 0, 1]] where
  M :=![![![-19471907820243, 209192554684, 1393818964300], ![-97567327501000, -19471907820243, 1603011518984], ![-112210806328880, -97567327501000, -17868896301259]]]
  hmulB := by decide  
  f := ![![![504343051488183746525569937, -132253151300318878518752844, 27475652465800311158445956]], ![![-31538261021712216828968174, 8270232720260206534071181, -1718144617341998104945344]], ![![687689696745548047529680365, -180331877762551508415863380, 37464029803402515797462481]]]
  g := ![![![-1887440242659, 209192554684, 1393818964300], ![-3403406890866, -19471907820243, 1603011518984], ![18263664007055, -97567327501000, -17868896301259]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![504343051488183746525569937, -132253151300318878518752844, 27475652465800311158445956]] ![![-19471907820243, 209192554684, 1393818964300]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [8, 19, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 13, 3], [17, 17, 28], [0, 1]]
 g := ![![[7, 10, 7], [19, 26, 1], [7, 9, 2], [1]], ![[28, 9, 9, 27], [14, 20, 1, 15], [6, 21, 3, 23], [7, 28, 11, 27]], ![[24, 3, 2, 8], [5, 29, 0, 8], [30, 6, 3, 7], [27, 8, 24, 4]]]
 h' := ![![[6, 13, 3], [3, 25, 10], [6, 14, 30], [23, 12, 23], [0, 1]], ![[17, 17, 28], [2, 25, 28], [9, 26, 25], [5, 24, 24], [6, 13, 3]], ![[0, 1], [2, 12, 24], [20, 22, 7], [16, 26, 15], [17, 17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 15], []]
 b := ![[], [8, 22, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [8, 19, 8, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-585094, -79918, 8308]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18874, -2578, 268]
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



lemma PB103I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB103I0 : PrimesBelowBoundCertificateInterval O 1 31 103 where
  m := 11
  g := ![3, 1, 3, 3, 2, 2, 3, 1, 3, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB103I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0, I23N0, I23N1]
    · exact ![I29N0, I29N1]
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
    · exact ![2, 2, 2]
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![6859]
    · exact ![23, 23, 23]
    · exact ![841, 29]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
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
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I11N1, I13N1, I17N0, I17N1, I17N2, I23N0, I23N1, I29N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0], [I5N0, I5N0, I5N1], [I7N0, I7N0, I7N1], [I11N1], [I13N1], [I17N0, I17N1, I17N2], [], [I23N0, I23N0, I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
