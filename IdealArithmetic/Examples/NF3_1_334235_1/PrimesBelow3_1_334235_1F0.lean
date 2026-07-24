
import IdealArithmetic.Examples.NF3_1_334235_1.RI3_1_334235_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9070, -3425, 362]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![9070, -3425, 362]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![9070, -3425, 362], ![-76744, 28980, -3063], ![649356, -245209, 25917]]]
  hmulB := by decide  
  f := ![![![-507, 67, 15]], ![![-1590, 159, 41]], ![![-8692, 665, 200]]]
  g := ![![![4535, -3425, 362], ![-38372, 28980, -3063], ![324678, -245209, 25917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-507, 67, 15]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-507, 67, 15]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![-507, 67, 15], ![-3180, 318, 82], ![-17384, 1330, 400]]]
  hmulB := by decide  
  f := ![![![9070, -3425, 362]], ![![-76744, 28980, -3063]], ![![290841, -109827, 11608]]]
  g := ![![![-261, 26, 15], ![-1631, 118, 82], ![-8892, 465, 400]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![637, -2071, 493]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![72, -1282, 493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![9070, -3425, 362]] ![![-507, 67, 15]]
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 1], [2, 2, 2], [0, 1]]
 g := ![![[1]], ![[0, 1, 1, 1]], ![[2, 2, 2, 2]]]
 h' := ![![[2, 0, 1], [0, 1]], ![[2, 2, 2], [2, 0, 1]], ![[0, 1], [2, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [1, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 0, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-350835, 89319, -25719]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-116945, 29773, -8573]
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


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19546491, 1644220, 467341]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-19546491, 1644220, 467341]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![-19546491, 1644220, 467341], ![-99076292, 6157264, 2111561], ![-447650932, 17059563, 8268825]]]
  hmulB := by decide  
  f := ![![![14891030586957, -5623134209517, 594328912396]], ![![-22221339768199, 8391197311844, -886895276945]], ![![225134169067496, -85014911521535, 8985526224240]]]
  g := ![![![-4612015, 1644220, 467341], ![-22735960, 6157264, 2111561], ![-99557159, 17059563, 8268825]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![312772596756395235357053045, -118108835943218427557857634, 12483339965759069810534293]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![312772596756395235357053045, -118108835943218427557857634, 12483339965759069810534293]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![312772596756395235357053045, -118108835943218427557857634, 12483339965759069810534293], ![-2646468072740922799833270116, 999356294873144074936439160, -105625495977459357747323341], ![22392605147221383842432548292, -8455870351501187475936053871, 893730798895684717189115819]]]
  hmulB := by decide  
  f := ![![![9956455369029, -14042201585957, -1798644878686]], ![![80245125003898, -23410683226123, -3887627244403]], ![![673643181174669, -100795208571978, -21321700860406]]]
  g := ![![![107301385735414604132446804, -118108835943218427557857634, 12483339965759069810534293], ![-907911033301950318391765019, 999356294873144074936439160, -105625495977459357747323341], ![7682123010265614815423108043, -8455870351501187475936053871, 893730798895684717189115819]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-19546491, 1644220, 467341]] ![![-19546491, 1644220, 467341]]
  ![![9956455369029, -14042201585957, -1798644878686]] where
 M := ![![![9956455369029, -14042201585957, -1798644878686]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![9956455369029, -14042201585957, -1798644878686]] ![![312772596756395235357053045, -118108835943218427557857634, 12483339965759069810534293]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 0, 2], [1, 6, 5], [0, 1]]
 g := ![![[1], [1]], ![[6, 2, 0, 1], [6, 1, 0, 1]], ![[4, 1, 2, 6], [3, 0, 2, 6]]]
 h' := ![![[6, 0, 2], [6, 6], [0, 1]], ![[1, 6, 5], [0, 0, 5], [6, 0, 2]], ![[0, 1], [5, 1, 2], [1, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-898877, 544208, -76454]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-128411, 77744, -10922]
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


def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-230412224473, 87008004863, -9196183298]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-230412224473, 87008004863, -9196183298]] 
 ![![11, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![-230412224473, 87008004863, -9196183298], ![1949590859176, -736202305863, 77811821565], ![-16496106171780, 6229241045251, -658390484298]]]
  hmulB := by decide  
  f := ![![![7798641, -723376, -194421]], ![![5873925, -460422, -136460]], ![![19106386, -973485, -381923]]]
  g := ![![![-43003988406, 87008004863, -9196183298], ![363870375785, -736202305863, 77811821565], ![-3078822576267, 6229241045251, -658390484298]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-526276551277891592092385, 198731958938382733188894, -21004682551285006991444]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-526276551277891592092385, 198731958938382733188894, -21004682551285006991444]] 
 ![![11, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![-526276551277891592092385, 198731958938382733188894, -21004682551285006991444], ![4452992700872421482186128, -1681534091598566976621805, 177727276387097726197450], ![-37678182594064717953859400, 14227992902162796423045878, -1503806815211469250424355]]]
  hmulB := by decide  
  f := ![![![-5156759449675, 1103692354462, 202467716120]], ![![-5777290328740, 944884941343, 192366448642]], ![![-27986044696494, 3230709290122, 772721027657]]]
  g := ![![![-108652390156701134809027, 198731958938382733188894, -21004682551285006991444], ![919342309904009366498968, -1681534091598566976621805, 177727276387097726197450], ![-7778846664677008013045162, 14227992902162796423045878, -1503806815211469250424355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-230412224473, 87008004863, -9196183298]] ![![-230412224473, 87008004863, -9196183298]]
  ![![374421020201599851231057, -141388444215674457441766, 14943843974743436577353]] where
 M := ![![![374421020201599851231057, -141388444215674457441766, 14943843974743436577353]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI11N1 : IdealMulLeCertificate' Table 
  ![![374421020201599851231057, -141388444215674457441766, 14943843974743436577353]] ![![-526276551277891592092385, 198731958938382733188894, -21004682551285006991444]]
  ![![11, 0, 0]] where
 M := ![![![-1389707595255350711105349728466407991373644391193, 524779817922788411036812786611551421758028389522, -55465832187599829881665038554966303105291405323]]]
 hmul := by decide  
 g := ![![![![-126337054114122791918668157133309817397604035563, 47707256174798946457892071510141038341638944502, -5042348380690893625605912595906027555026491393]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-260265807101, -7781041286, 2715706127]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-260265807101, -7781041286, 2715706127]] 
 ![![13, 0, 0], ![0, 13, 0], ![3, 2, 1]] where
  M :=![![![-260265807101, -7781041286, 2715706127], ![-575729698924, -110901970116, -5065335159], ![1073851053708, -854323132669, -115967305275]]]
  hmulB := by decide  
  f := ![![![-656428432537368611733, 247879765845998288201, -26199287826153728862]], ![![5554249019144590518744, -2097389262975823699143, 221680478019844559339]], ![![-2912080661502305490583, 1099656621678645288362, -116226591722673169824]]]
  g := ![![![-20647148114, -1016342580, 2715706127], ![-43117976419, -7751638446, -5065335159], ![109365613041, -47876040163, -115967305275]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[8, 4], [9], [4, 1]], ![[11, 9], [9], [8, 12]]]
 h' := ![![[4, 12], [2, 11], [2, 10], [0, 1]], ![[0, 1], [7, 2], [3, 3], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [6, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [6, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-630, -56, 50]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, -12, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![70288669634869, -9368481640166, -2088982365717]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![70288669634869, -9368481640166, -2088982365717]] 
 ![![13, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![70288669634869, -9368481640166, -2088982365717], ![442864261532004, -44605360479566, -11457464005883], ![2428982369247196, -187296258791561, -56062824485449]]]
  hmulB := by decide  
  f := ![![![-354762352135234342054081771, 133964960107439275145630297, -14159229723714316195657756]], ![![-41989755378839106697028726, 15856124164220847587772663, -1675889757955246385123463]], ![![-2062912634606971435816192752, 778994747150928067408496555, -82334705803896464511378218]]]
  g := ![![![13256108884569, -9368481640166, -2088982365717], ![71903670950092, -44605360479566, -11457464005883], ![348168942700354, -187296258791561, -56062824485449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-260265807101, -7781041286, 2715706127]] ![![70288669634869, -9368481640166, -2088982365717]]
  ![![13, 0, 0]] where
 M := ![![![-15143280133109569436952021, 2276729989292700231386395, 480591525943666455795932]]]
 hmul := by decide  
 g := ![![![![-1164867702546889956688617, 175133076099438479337415, 36968578918743573522764]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [2, 13, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 15, 13], [0, 1, 4], [0, 1]]
 g := ![![[10, 3, 9], [13, 16], [14, 1], []], ![[3, 2], [13, 1], [7, 1], [2, 16]], ![[0, 12, 5, 2], [9, 9], [8, 4], [11, 16]]]
 h' := ![![[14, 15, 13], [10, 5, 3], [6, 3, 13], [0, 0, 1], [0, 1]], ![[0, 1, 4], [10, 5], [11, 8, 1], [5, 5, 1], [14, 15, 13]], ![[0, 1], [12, 7, 14], [9, 6, 3], [12, 12, 15], [0, 1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 4], []]
 b := ![[], [15, 8, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [2, 13, 3, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2388585, 365279, 67269]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-140505, 21487, 3957]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23895544261, -9023408528, 953715913]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![23895544261, -9023408528, 953715913]] 
 ![![19, 0, 0], ![0, 19, 0], ![17, 10, 1]] where
  M :=![![![23895544261, -9023408528, 953715913], ![-202187773556, 76349919476, -8069692615], ![1710774834380, -646020867381, 68280226861]]]
  hmulB := by decide  
  f := ![![![639659, -13855, -10572]], ![![2241264, 58199, -24427]], ![![2024493, 65486, -20538]]]
  g := ![![![404335460, -976871982, 953715913], ![-3421210479, 8265623454, -8069692615], ![28947946197, -69938059789, 68280226861]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18], [0, 1]]
 g := ![![[15, 5], [17, 9], [9], [1]], ![[0, 14], [9, 10], [9], [1]]]
 h' := ![![[16, 18], [8, 9], [18, 16], [15, 16], [0, 1]], ![[0, 1], [0, 10], [8, 3], [5, 3], [16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [14, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1062, -484, 58]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, -56, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-639659, 13855, 10572]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-639659, 13855, 10572]] 
 ![![19, 0, 0], ![8, 1, 0], ![12, 0, 1]] where
  M :=![![![-639659, 13855, 10572], ![-2241264, -58199, 24427], ![-5178524, -897779, -33772]]]
  hmulB := by decide  
  f := ![![![-23895544261, 9023408528, -953715913]], ![![580179972, -219086908, 23156069]], ![![-105132703448, 39700093143, -4196043043]]]
  g := ![![![-46177, 13855, 10572], ![-108884, -58199, 24427], ![126788, -897779, -33772]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![23895544261, -9023408528, 953715913]] ![![-639659, 13855, 10572]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [3, 22, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 12, 4], [20, 10, 19], [0, 1]]
 g := ![![[9, 5, 1], [5, 21, 18], [4, 16, 1], []], ![[8, 5, 3, 1], [10, 13, 8, 18], [2, 19, 21, 9], [7, 16]], ![[20, 3, 4, 22], [7, 16, 3, 5], [2, 5, 2, 22], [15, 16]]]
 h' := ![![[19, 12, 4], [8, 17, 22], [11, 2, 8], [0, 0, 1], [0, 1]], ![[20, 10, 19], [14, 19, 12], [9, 9, 19], [18, 1, 10], [19, 12, 4]], ![[0, 1], [16, 10, 12], [16, 12, 19], [10, 22, 12], [20, 10, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 8], []]
 b := ![[], [1, 16, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [3, 22, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15479, -108721, 22908]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![673, -4727, 996]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16593, -18266, -1927]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-16593, -18266, -1927]] 
 ![![29, 0, 0], ![0, 29, 0], ![16, 22, 1]] where
  M :=![![![-16593, -18266, -1927], ![408524, -122578, -20193], ![4280916, -702091, -142771]]]
  hmulB := by decide  
  f := ![![![114595175, -43273301, 4573708]], ![![-969626096, 366149115, -38699593]], ![![-389446124, 147062207, -15543524]]]
  g := ![![![491, 832, -1927], ![25228, 11092, -20193], ![226388, 84099, -142771]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [26, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 28], [0, 1]]
 g := ![![[28, 4], [6], [19, 28], [26, 1]], ![[16, 25], [6], [22, 1], [23, 28]]]
 h' := ![![[26, 28], [19, 27], [28, 21], [20, 12], [0, 1]], ![[0, 1], [25, 2], [23, 8], [13, 17], [26, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [4, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [26, 3, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7668, -2898, 298]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![100, -326, 298]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-114595175, 43273301, -4573708]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-114595175, 43273301, -4573708]] 
 ![![29, 0, 0], ![6, 1, 0], ![22, 0, 1]] where
  M :=![![![-114595175, 43273301, -4573708], ![969626096, -366149115, 38699593], ![-8204313716, 3098103711, -327449522]]]
  hmulB := by decide  
  f := ![![![16593, 18266, 1927]], ![![-10654, 8006, 1095]], ![![-135030, 38067, 6385]]]
  g := ![![![-9434945, 43273301, -4573708], ![79832060, -366149115, 38699593], ![-675484362, 3098103711, -327449522]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-16593, -18266, -1927]] ![![-114595175, 43273301, -4573708]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5785194244961271, -2184598539206300, 230897934399452]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![5785194244961271, -2184598539206300, 230897934399452]] 
 ![![31, 0, 0], ![2, 1, 0], ![27, 0, 1]] where
  M :=![![![5785194244961271, -2184598539206300, 230897934399452], ![-48950362092683824, 18484580636931131, -1953700604806848], ![414184528219051776, -156403895357060464, 16530880032124283]]]
  hmulB := by decide  
  f := ![![![2126496601, -115882828, -43397812]], ![![433978366, -15875765, -7937944]], ![![2941383997, -86739852, -51335633]]]
  g := ![![![126456357889957, -2184598539206300, 230897934399452], ![-1069987323766490, 18484580636931131, -1953700604806848], ![9053501873090873, -156403895357060464, 16530880032124283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5873925, -460422, -136460]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![5873925, -460422, -136460]] 
 ![![31, 0, 0], ![3, 1, 0], ![22, 0, 1]] where
  M :=![![![5873925, -460422, -136460], ![28929520, -1631375, -596882], ![126538984, -3898990, -2228257]]]
  hmulB := by decide  
  f := ![![![1307885814195, -493882369054, 52200171704]], ![![-230412224473, 87008004863, -9196183298]], ![![3948713346790, -1491108689506, 157600543163]]]
  g := ![![![330881, -460422, -136460], ![1514679, -1631375, -596882], ![6040568, -3898990, -2228257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, -42, -4]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-69, -42, -4]] 
 ![![31, 0, 0], ![25, 1, 0], ![26, 0, 1]] where
  M :=![![![-69, -42, -4], ![848, -289, -46], ![9752, -1682, -335]]]
  hmulB := by decide  
  f := ![![![-19443, 7342, -776]], ![![-10373, 3917, -414]], ![![-61210, 23114, -2443]]]
  g := ![![![35, -42, -4], ![299, -289, -46], ![1952, -1682, -335]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![5785194244961271, -2184598539206300, 230897934399452]] ![![5873925, -460422, -136460]]
  ![![19443, -7342, 776]] where
 M := ![![![19443, -7342, 776]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![19443, -7342, 776]] ![![-69, -42, -4]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB164I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB164I0 : PrimesBelowBoundCertificateInterval O 1 31 164 where
  m := 11
  g := ![2, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB164I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
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
    · exact ![2, 4]
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![841, 29]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I11N0, I11N1, I13N1, I19N1, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N1], [I3N0], [I5N0, I5N0, I5N1], [], [I11N0, I11N0, I11N1], [I13N1], [], [I19N1], [], [I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
