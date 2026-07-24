
import IdealArithmetic.Examples.NF3_1_89544_1.RI3_1_89544_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36370, 3753, -800]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![36370, 3753, -800]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![36370, 3753, -800], ![52800, 25170, 2953], ![-194898, 94142, 28123]]]
  hmulB := by decide  
  f := ![![![-429854584, 180859219, -31218609]], ![![1030214097, -433457555, 74820305]], ![![-4938140130, 2077698367, -358637250]]]
  g := ![![![18185, 3753, -800], ![26400, 25170, 2953], ![-97449, 94142, 28123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![432873064584795941, -182129229979165996, 31437829100603873]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![432873064584795941, -182129229979165996, 31437829100603873]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![432873064584795941, -182129229979165996, 31437829100603873], ![-2074896720639855618, 873002671993250163, -150691400878562123], ![9945632457985100118, -4184576332939725340, 722311271114688040]]]
  hmulB := by decide  
  f := ![![![1676853700, 155646020, -40511791]], ![![2175315953, 632667323, 37311219]], ![![-2961002707, 2220651716, 592155532]]]
  g := ![![![291782232731679032, -182129229979165996, 31437829100603873], ![-1398603995877271829, 873002671993250163, -150691400878562123], ![6703948759905068709, -4184576332939725340, 722311271114688040]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![36370, 3753, -800]] ![![36370, 3753, -800]]
  ![![1676853700, 155646020, -40511791]] where
 M := ![![![1676853700, 155646020, -40511791]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1676853700, 155646020, -40511791]] ![![432873064584795941, -182129229979165996, 31437829100603873]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, -29, 5]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![69, -29, 5]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![69, -29, 5], ![-330, 139, -24], ![1584, -666, 115]]]
  hmulB := by decide  
  f := ![![![1, 5, 1]], ![![-22, 5, 2]], ![![-132, 6, 7]]]
  g := ![![![23, -29, 5], ![-110, 139, -24], ![528, -666, 115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3934278177001543, -341706650054430, 99947092152082]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-3934278177001543, -341706650054430, 99947092152082]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-3934278177001543, -341706650054430, 99947092152082], ![-6596508082037412, -2535018886872395, -241759557902348], ![15956130821554968, -9981141892670284, -2776778444774743]]]
  hmulB := by decide  
  f := ![![![-4626149350831556320654126492653, 1946429768837050507825249392778, -335978614942954932629492378030]], ![![5849479745134489744297456819109, -2461140063731958289880590130765, 424824179650380214188754878906]], ![![-38514024952891140201409405319558, 16204588092808821540645864647336, -2797118678674913222510082508795]]]
  g := ![![![-1264155237083759, -341706650054430, 99947092152082], ![-1192656693120107, -2535018886872395, -241759557902348], ![10496943201258246, -9981141892670284, -2776778444774743]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![69, -29, 5]] ![![-3934278177001543, -341706650054430, 99947092152082]]
  ![![-385805726246679, 32079402192365, 23484313788035]] where
 M := ![![![-385805726246679, 32079402192365, 23484313788035]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-385805726246679, 32079402192365, 23484313788035]] ![![-3934278177001543, -341706650054430, 99947092152082]]
  ![![3, 0, 0]] where
 M := ![![![1680973796562009778052084074197, -183889776320022336331360778145, -111526398882717403592920208703]]]
 hmul := by decide  
 g := ![![![![560324598854003259350694691399, -61296592106674112110453592715, -37175466294239134530973402901]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 3, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 2], [1, 0, 3], [0, 1]]
 g := ![![[2, 0, 1], []], ![[0, 3], [1, 4]], ![[2, 3, 2, 3], [0, 4]]]
 h' := ![![[4, 4, 2], [0, 0, 1], [0, 1]], ![[1, 0, 3], [3, 2], [4, 4, 2]], ![[0, 1], [1, 3, 4], [1, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3], []]
 b := ![[], [3, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 3, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![795, 1215, -45]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![159, 243, -9]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23083247107, -352899476, -1078297024]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![23083247107, -352899476, -1078297024]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![23083247107, -352899476, -1078297024], ![71167603584, 7987088771, -1431196500], ![94458969000, 51130852584, 6555892271]]]
  hmulB := by decide  
  f := ![![![125540790801826544941, -52820675228761560020, 9117522547096151504]], ![![-14227617843005688500, 5986200792303775131, -1033294641897257500]], ![![501730290142721383823, -211100571685067074084, 36438652359284002143]]]
  g := ![![![4269475733, -352899476, -1078297024], ![6625033000, 7987088771, -1431196500], ![-20406271813, 51130852584, 6555892271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5529023353, 943959363, -43712363]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![5529023353, 943959363, -43712363]] 
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![5529023353, 943959363, -43712363], ![2885015958, 4917050271, 900247000], ![-59416302000, 15488473958, 5817297271]]]
  hmulB := by decide  
  f := ![![![14660490907590484441, -6168330022282941127, 1064732470997861373]], ![![432873064584795941, -182129229979165996, 31437829100603873]], ![![54402701586798102441, -22889671267242684365, 3951049337609864004]]]
  g := ![![![134337661, 943959363, -43712363], ![-3485853771, 4917050271, 900247000], ![-22044366229, 15488473958, 5817297271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![23083247107, -352899476, -1078297024]] ![![23083247107, -352899476, -1078297024]]
  ![![405866461827046291465, -66098951426400109944, -31454727290315577072]] where
 M := ![![![405866461827046291465, -66098951426400109944, -31454727290315577072]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![405866461827046291465, -66098951426400109944, -31454727290315577072]] ![![5529023353, 943959363, -43712363]]
  ![![7, 0, 0]] where
 M := ![![![3922272191978022815454862839793, -429076144746718784773175149005, -260228264059673941716813820307]]]
 hmul := by decide  
 g := ![![![![560324598854003259350694691399, -61296592106674112110453592715, -37175466294239134530973402901]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6067, 1802, 640]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-6067, 1802, 640]] 
 ![![11, 0, 0], ![0, 11, 0], ![8, 10, 1]] where
  M :=![![![-6067, 1802, 640], ![-42240, 2893, 2442], ![-161172, -8052, 5335]]]
  hmulB := by decide  
  f := ![![![-3190649, 1342450, -231724]], ![![15293784, -6434785, 1110726]], ![![4918612, -2069482, 357219]]]
  g := ![![![-1017, -418, 640], ![-5616, -1957, 2442], ![-18532, -5582, 5335]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[9, 4], [4, 3], [1]], ![[0, 7], [0, 8], [1]]]
 h' := ![![[6, 10], [10, 2], [8, 6], [0, 1]], ![[0, 1], [0, 9], [0, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [3, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [3, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![197, -642, 136]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81, -182, 136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3190649, -1342450, 231724]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![3190649, -1342450, 231724]] 
 ![![11, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![3190649, -1342450, 231724], ![-15293784, 6434785, -1110726], ![73307916, -30843948, 5324059]]]
  hmulB := by decide  
  f := ![![![6067, -1802, -640]], ![![3840, -263, -222]], ![![14652, 732, -485]]]
  g := ![![![290059, -1342450, 231724], ![-1390344, 6434785, -1110726], ![6664356, -30843948, 5324059]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-6067, 1802, 640]] ![![3190649, -1342450, 231724]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2884092898213, -1213468015719, 209460063613]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![2884092898213, -1213468015719, 209460063613]] 
 ![![13, 0, 0], ![1, 1, 0], ![12, 0, 1]] where
  M :=![![![2884092898213, -1213468015719, 209460063613], ![-13824364198458, 5816533788795, -1004007952106], ![66264524838996, -27880475527942, 4812525836689]]]
  hmulB := by decide  
  f := ![![![-12646097, -60055, 537879]], ![![-3703547, -398142, 78131]], ![![-14099196, -2271626, 139737]]]
  g := ![![![121849242352, -1213468015719, 209460063613], ![-584061735537, 5816533788795, -1004007952106], ![2799591563590, -27880475527942, 4812525836689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145790132294427310307773, 61340486867238104191714, -10588150750435069359818]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-145790132294427310307773, 61340486867238104191714, -10588150750435069359818]] 
 ![![13, 0, 0], ![12, 1, 0], ![12, 0, 1]] where
  M :=![![![-145790132294427310307773, 61340486867238104191714, -10588150750435069359818], ![698817949528714577747988, -294024242800518281345225, 50752336116803034831896], ![-3349654183709000298905136, 1409350655163957065394532, -243271906683715246513329]]]
  hmulB := by decide  
  f := ![![![838524588647, -459434640730, -132344940694]], ![![1445927780736, -502116943833, -167686066904]], ![![3778442110596, -389489518684, -245709496217]]]
  g := ![![![-58062935822774132945425, 61340486867238104191714, -10588150750435069359818], ![278313909979484425839072, -294024242800518281345225, 50752336116803034831896], ![-1334046089651684778883044, 1409350655163957065394532, -243271906683715246513329]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![2884092898213, -1213468015719, 209460063613]] ![![-145790132294427310307773, 61340486867238104191714, -10588150750435069359818]]
  ![![-1970084294144559909576469071408749389, 828903354914821273148141922467962973, -143079296034525941957909118789176135]] where
 M := ![![![-1970084294144559909576469071408749389, 828903354914821273148141922467962973, -143079296034525941957909118789176135]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-1970084294144559909576469071408749389, 828903354914821273148141922467962973, -143079296034525941957909118789176135]] ![![-145790132294427310307773, 61340486867238104191714, -10588150750435069359818]]
  ![![13, 0, 0]] where
 M := ![![![1345737555277744992751206265824325894158314565240270685078381, -566212510662622916351304587361507732100784330901962380610491, 97735504327732617864541995458905020250129140371328042241425]]]
 hmul := by decide  
 g := ![![![![103518273482903460980862020448025068781408812710790052698337, -43554808512509455103946506720115979392368025453997106200807, 7518115717517893681887845804531155403856087720871387864725]]]]
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
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6161, -771, -429]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![6161, -771, -429]] 
 ![![17, 0, 0], ![0, 17, 0], ![11, 10, 1]] where
  M :=![![![6161, -771, -429], ![28314, 155, -1200], ![79200, 11514, -1045]]]
  hmulB := by decide  
  f := ![![![-803225, 337953, -58335]], ![![3850110, -1619915, 279618]], ![![659461, -277465, 47894]]]
  g := ![![![640, 207, -429], ![2442, 715, -1200], ![5335, 1292, -1045]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [8, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[10, 15], [2], [8], [1]], ![[0, 2], [2], [8], [1]]]
 h' := ![![[5, 16], [1, 10], [0, 11], [9, 5], [0, 1]], ![[0, 1], [0, 7], [4, 6], [0, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [8, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3402, -196, 130]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![116, -88, 130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-803225, 337953, -58335]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-803225, 337953, -58335]] 
 ![![17, 0, 0], ![6, 1, 0], ![15, 0, 1]] where
  M :=![![![-803225, 337953, -58335], ![3850110, -1619915, 279618], ![-18454788, 7764762, -1340297]]]
  hmulB := by decide  
  f := ![![![6161, -771, -429]], ![![3840, -263, -222]], ![![10095, -3, -440]]]
  g := ![![![-115054, 337953, -58335], ![551490, -1619915, 279618], ![-2643465, 7764762, -1340297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![6161, -771, -429]] ![![-803225, 337953, -58335]]
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
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1046251, 440205, -75985]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-1046251, 440205, -75985]] 
 ![![19, 0, 0], ![0, 19, 0], ![4, 11, 1]] where
  M :=![![![-1046251, 440205, -75985], ![5015010, -2110041, 364220], ![-24038520, 10114090, -1745821]]]
  hmulB := by decide  
  f := ![![![-1519, -245, 15]], ![![-990, -1309, -230]], ![![-94, -1031, -211]]]
  g := ![![![-39069, 67160, -75985], ![187270, -321919, 364220], ![-897644, 1543059, -1745821]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 18], [0, 1]]
 g := ![![[9, 11], [6, 1], [17], [1]], ![[0, 8], [0, 18], [17], [1]]]
 h' := ![![[13, 18], [15, 12], [6, 1], [12, 13], [0, 1]], ![[0, 1], [0, 7], [0, 18], [10, 6], [13, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [4, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [7, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-184, -544, 106]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -90, 106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1519, -245, 15]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-1519, -245, 15]] 
 ![![19, 0, 0], ![7, 1, 0], ![8, 0, 1]] where
  M :=![![![-1519, -245, 15], ![-990, -1309, -230], ![15180, -4210, -1539]]]
  hmulB := by decide  
  f := ![![![-1046251, 440205, -75985]], ![![-121513, 51126, -8825]], ![![-1705712, 717670, -123879]]]
  g := ![![![4, -245, 15], ![527, -1309, -230], ![2998, -4210, -1539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-1046251, 440205, -75985]] ![![-1519, -245, 15]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [19, 15, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 5, 3], [18, 17, 20], [0, 1]]
 g := ![![[11, 8, 4], [0, 7, 12], [11, 16, 1], []], ![[18, 10, 16, 8], [18, 3, 19, 18], [19, 2, 3, 16], [13, 9]], ![[20, 9, 15, 7], [14, 4, 19, 19], [0, 17, 19, 17], [19, 9]]]
 h' := ![![[21, 5, 3], [0, 9, 2], [21, 14, 9], [0, 0, 1], [0, 1]], ![[18, 17, 20], [2, 9, 15], [14, 0, 11], [10, 5, 17], [21, 5, 3]], ![[0, 1], [19, 5, 6], [9, 9, 3], [9, 18, 5], [18, 17, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 14], []]
 b := ![[], [21, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [19, 15, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-575, 1035, 69]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, 45, 3]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54619, 81073, 19291]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-54619, 81073, 19291]] 
 ![![29, 0, 0], ![0, 29, 0], ![27, 3, 1]] where
  M :=![![![-54619, 81073, 19291], ![-1273206, 215455, 100364], ![-6624024, 131890, 315819]]]
  hmulB := by decide  
  f := ![![![-1889923265, 795175993, -137257523]], ![![9058996518, -3811528587, 657918470]], ![![-2319777849, 976035212, -168476132]]]
  g := ![![![-19844, 800, 19291], ![-137346, -2953, 100364], ![-522453, -28123, 315819]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [20, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 28], [0, 1]]
 g := ![![[5, 16], [25], [16, 16], [16, 1]], ![[0, 13], [25], [11, 13], [3, 28]]]
 h' := ![![[16, 28], [23, 4], [28, 24], [28, 4], [0, 1]], ![[0, 1], [0, 25], [6, 5], [5, 25], [16, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [8, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [20, 13, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2540, 765, 429]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-487, -18, 429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1889923265, -795175993, 137257523]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![1889923265, -795175993, 137257523]] 
 ![![29, 0, 0], ![25, 1, 0], ![13, 0, 1]] where
  M :=![![![1889923265, -795175993, 137257523], ![-9058996518, 3811528587, -657918470], ![43422619020, -18269855098, 3153610117]]]
  hmulB := by decide  
  f := ![![![54619, -81073, -19291]], ![![90989, -77320, -20091]], ![![252899, -40891, -19538]]]
  g := ![![![689137079, -795175993, 137257523], ![-3303250727, 3811528587, -657918470], ![15833519481, -18269855098, 3153610117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-54619, 81073, 19291]] ![![1889923265, -795175993, 137257523]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1932297419, -236998416, -133544724]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1932297419, -236998416, -133544724]] 
 ![![31, 0, 0], ![0, 31, 0], ![13, 13, 1]] where
  M :=![![![1932297419, -236998416, -133544724], ![8813951784, 62671283, -370543140], ![24455847240, 3626347824, -307871857]]]
  hmulB := by decide  
  f := ![![![-42723341456753059, 17975637474969648, -3102824400987972]], ![![204786410465206152, -86162883070584667, 14872813073981676]], ![![36297233362164503, -15271883846517601, 2636122024268231]]]
  g := ![![![118334801, 48357516, -133544724], ![439710084, 157410713, -370543140], ![918005851, 246086515, -307871857]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [15, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 30], [0, 1]]
 g := ![![[4, 9], [15, 7], [3, 28], [2, 1]], ![[22, 22], [29, 24], [28, 3], [4, 30]]]
 h' := ![![[2, 30], [23, 28], [17, 21], [1, 20], [0, 1]], ![[0, 1], [17, 3], [28, 10], [10, 11], [2, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [21, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [15, 29, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![317, -55, -9]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 2, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42723341456753059, 17975637474969648, -3102824400987972]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-42723341456753059, 17975637474969648, -3102824400987972]] 
 ![![31, 0, 0], ![17, 1, 0], ![21, 0, 1]] where
  M :=![![![-42723341456753059, 17975637474969648, -3102824400987972], ![204786410465206152, -86162883070584667, 14872813073981676], ![-981605662882790616, 413005793500949616, -71290069996602991]]]
  hmulB := by decide  
  f := ![![![1932297419, -236998416, -133544724]], ![![1343967997, -127945219, -85187208]], ![![2097873969, -43568352, -100397131]]]
  g := ![![![-9133866648725473, 17975637474969648, -3102824400987972], ![43781495100371945, -86162883070584667, 14872813073981676], ![-209858473628073267, 413005793500949616, -71290069996602991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1932297419, -236998416, -133544724]] ![![-42723341456753059, 17975637474969648, -3102824400987972]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB85I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB85I0 : PrimesBelowBoundCertificateInterval O 1 31 85 where
  m := 11
  g := ![3, 3, 1, 3, 2, 3, 2, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB85I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
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
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![961, 31]
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
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
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
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
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
  β := ![I2N0, I2N1, I3N0, I3N1, I7N0, I7N1, I11N1, I13N0, I13N1, I17N1, I19N1, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N1, I3N1], [], [I7N0, I7N0, I7N1], [I11N1], [I13N0, I13N1, I13N1], [I17N1], [I19N1], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
