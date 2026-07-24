
import IdealArithmetic.Examples.NF3_1_597915_1.RI3_1_597915_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48, 3, -4]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![48, 3, -4]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![48, 3, -4], ![-678, -11, 36], ![1009, -9, -37]]]
  hmulB := by decide  
  f := ![![![-731, -147, -64]], ![![-5619, -1130, -492]], ![![-8966, -1803, -785]]]
  g := ![![![26, 3, -4], ![-357, -11, 36], ![523, -9, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-731, -147, -64]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-731, -147, -64]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 2]] where
  M :=![![![-731, -147, -64], ![-11238, -2260, -984], ![-17201, -3459, -1506]]]
  hmulB := by decide  
  f := ![![![48, 3, -4]], ![![-315, -4, 16]], ![![1009, -9, -37]]]
  g := ![![![-292, -147, -32], ![-4489, -2260, -492], ![-6871, -3459, -753]]]
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
  c := ![-3873, 1849, 1508]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2861, 1849, 754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![48, 3, -4]] ![![-731, -147, -64]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1738055623159, 495921869498, -397882658672]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![1738055623159, 495921869498, -397882658672]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![1738055623159, 495921869498, -397882658672], ![-67046090893916, -3538183965771, 5161022932000], ![134140089359486, 2462431901386, -7309480500103]]]
  hmulB := by decide  
  f := ![![![13153619192038716330222413, 2645172282948045939838902, 1151682097787883203819888]], ![![67409327762541373244292884, 13555910567758956204892405, 5902110656740239302417184]], ![![107556499816819018256336181, 21629444186627691658132852, 9417248099650747529034489]]]
  g := ![![![711979427277, 495921869498, -397882658672], ![-24069037941972, -3538183965771, 5161022932000], ![47149856619863, 2462431901386, -7309480500103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![1738055623159, 495921869498, -397882658672]] ![![1738055623159, 495921869498, -397882658672]]
  ![![-83600800778300984140397479, -1872481964726689098168168, 4776237483589288482594368]] where
 M := ![![![-83600800778300984140397479, -1872481964726689098168168, 4776237483589288482594368]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-83600800778300984140397479, -1872481964726689098168168, 4776237483589288482594368]] ![![1738055623159, 495921869498, -397882658672]]
  ![![3, 0, 0]] where
 M := ![![![620924676961756385990485756304589424575, -23073120201527671307458245744357423966, -11312428229089181764472677796593508016]]]
 hmul := by decide  
 g := ![![![![206974892320585461996828585434863141525, -7691040067175890435819415248119141322, -3770809409696393921490892598864502672]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-885863241825040, -178145714844502, -77562898986443]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-885863241825040, -178145714844502, -77562898986443]] 
 ![![5, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![-885863241825040, -178145714844502, -77562898986443], ![-13619547156370757, -2738869669128077, -1192477021796687], ![-20845117764090910, -4191920637153179, -1825121178033951]]]
  hmulB := by decide  
  f := ![![![140375746, 6335105, -10104763]], ![![-258823405, 1321081, 10136168]], ![![551484161, -4973869, -20186871]]]
  g := ![![![-23747480066441, -178145714844502, -77562898986443], ![-365101416719293, -2738869669128077, -1192477021796687], ![-558798463705904, -4191920637153179, -1825121178033951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2953719046931144, -250816679905672, 38350393520059]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![2953719046931144, -250816679905672, 38350393520059]] 
 ![![5, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![2953719046931144, -250816679905672, 38350393520059], ![6056283932118745, 2853225697055131, -2121584619805553], ![-47645101060357228, -3688627655595539, 4434826563529281]]]
  hmulB := by decide  
  f := ![![![-4827825410743534083145195562744, -970868152480833443484302565031, -422706482194957295705744423887]], ![![-18707169280654700157046336773143, -3761982535084728442906593744808, -1637930340408324968716032988827]], ![![-25617265302855683283547803349309, -5151592056508205661054443531785, -2242952712318018851643733038633]]]
  g := ![![![768386917198731, -250816679905672, 38350393520059], ![201627000662976, 2853225697055131, -2121584619805553], ![-9239014025712583, -3688627655595539, 4434826563529281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-885863241825040, -178145714844502, -77562898986443]] ![![-885863241825040, -178145714844502, -77562898986443]]
  ![![4827825410743534083145195562744, 970868152480833443484302565031, 422706482194957295705744423887]] where
 M := ![![![4827825410743534083145195562744, 970868152480833443484302565031, 422706482194957295705744423887]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![4827825410743534083145195562744, 970868152480833443484302565031, 422706482194957295705744423887]] ![![2953719046931144, -250816679905672, 38350393520059]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [2, 1, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4, 5], [5, 2, 2], [0, 1]]
 g := ![![[2, 6, 1], [1]], ![[1, 2, 5, 3], [3, 2, 5, 6]], ![[6, 5, 0, 1], [6, 3, 4, 1]]]
 h' := ![![[3, 4, 5], [5, 6, 1], [0, 1]], ![[5, 2, 2], [0, 3, 4], [3, 4, 5]], ![[0, 1], [1, 5, 2], [5, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 5], []]
 b := ![[], [6, 4, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [2, 1, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-394608673382, -90773277406, -33921549788]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56372667626, -12967611058, -4845935684]
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

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [10, 3, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 8, 10], [9, 2, 1], [0, 1]]
 g := ![![[9, 9, 3], [2, 7, 1], []], ![[5, 1, 0, 7], [3, 9, 9, 7], [2, 1]], ![[8, 6, 4, 9], [8, 1, 2, 9], [0, 1]]]
 h' := ![![[9, 8, 10], [2, 1, 5], [0, 0, 1], [0, 1]], ![[9, 2, 1], [8, 10, 9], [6, 7, 2], [9, 8, 10]], ![[0, 1], [9, 0, 8], [4, 4, 8], [9, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [3, 4, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [10, 3, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6882315, -1819103, -655281]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-625665, -165373, -59571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1063129655076784238919817494, 181878861383567307202175538, -164014195111757649979196099]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![1063129655076784238919817494, 181878861383567307202175538, -164014195111757649979196099]] 
 ![![13, 0, 0], ![0, 13, 0], ![5, 9, 1]] where
  M :=![![![1063129655076784238919817494, 181878861383567307202175538, -164014195111757649979196099], ![-27682669641343423532038181853, -1179475077672393889119989575, 1947073476403811407554992601], ![51439045490447958128992333274, 631727716844279472749042661, -2598776636197313032291435001]]]
  hmulB := by decide  
  f := ![![![-141167076388876497159277176720174535246645047478597178, -28388478659521659907735015771723472306257014037186623, -12360065492281061907482045088920182224555530071732801]], ![![-2170348156499104905994899741748798105011509670340682217, -436453625736219529309676990546988049982860100809614664, -190027632799330093539433990907027231776389522082294581]], ![![-1812365424628590677495799820406051291527836610917167004, -364463857270743708489961072171893197996286782090817669, -158683992878386757313119009977102582900362494294559674]]]
  g := ![![![144861586971967114524292153, 127538970568414319770380033, -164014195111757649979196099], ![-2878310540258652351524088066, -1438702797331284350547301768, 1947073476403811407554992601], ![4956379128571886406957654483, 1847747495586161289490150590, -2598776636197313032291435001]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 12], [0, 1]]
 g := ![![[5, 3], [3], [1, 1]], ![[8, 10], [3], [2, 12]]]
 h' := ![![[1, 12], [10, 4], [8, 9], [0, 1]], ![[0, 1], [1, 9], [4, 4], [1, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [2, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [5, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2692, 4245, 2504]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-756, -1407, 2504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![922255047128, 27003447035, -56836645373]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![922255047128, 27003447035, -56836645373]] 
 ![![13, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  M :=![![![922255047128, 27003447035, -56836645373], ![-9665059464713, 37042416892, 386537512399], ![11665333469237, -393491081000, -238651556064]]]
  hmulB := by decide  
  f := ![![![143258833169286214685912, 28809127682229975283240, 12543211955756481127681]], ![![268602846024799550428703, 54015612969531238250413, 23517868707106053002462]], ![![292367619281183135204564, 58794671767765132506155, 25598624088402990280398]]]
  g := ![![![65364150764, 27003447035, -56836645373], ![-858311827226, 37042416892, 386537512399], ![1224823682033, -393491081000, -238651556064]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![1063129655076784238919817494, 181878861383567307202175538, -164014195111757649979196099]] ![![922255047128, 27003447035, -56836645373]]
  ![![13, 0, 0]] where
 M := ![![![-2690673600167611005958771610653220839825, 99983520873286575665652398225548837186, 49020522326053120979381603785238534736]]]
 hmul := by decide  
 g := ![![![![-206974892320585461996828585434863141525, 7691040067175890435819415248119141322, 3770809409696393921490892598864502672]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![364961485940761444901, 73393185013166497042, 31954673736825177792]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![364961485940761444901, 73393185013166497042, 31954673736825177792]] 
 ![![17, 0, 0], ![2, 1, 0], ![16, 0, 1]] where
  M :=![![![364961485940761444901, 73393185013166497042, 31954673736825177792], ![5611035579023438396516, 1128370494506288958491, 491281458894856442960], ![8587855093885148947974, 1727004251276208116594, 751920731900940331823]]]
  hmulB := by decide  
  f := ![![![214822880853, 1487512882, -10101307552]], ![![-76158988466, 2972836287, 1294200624]], ![![290828996054, -6025393422, -8422671889]]]
  g := ![![![-17241156698516140815, 73393185013166497042, 31954673736825177792], ![-265071103076873094578, 1128370494506288958491, 491281458894856442960], ![-405699124651900740846, 1727004251276208116594, 751920731900940331823]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-731890, -28106, 49467]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-731890, -28106, 49467]] 
 ![![17, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![-731890, -28106, 49467], ![8402645, 24731, -373249], ![-10940034, 264203, 292301]]]
  hmulB := by decide  
  f := ![![![105842401578, 21284741707, 9267168017]], ![![120624989449, 24257497048, 10561476569]], ![![152729670551, 30713698293, 13372443341]]]
  g := ![![![-39349, -28106, 49467], ![510410, 24731, -373249], ![-722891, 264203, 292301]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84316, 12367, -4497]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-84316, 12367, -4497]] 
 ![![17, 0, 0], ![11, 1, 0], ![15, 0, 1]] where
  M :=![![![-84316, 12367, -4497], ![-744253, -123664, 112427], ![2672385, 142784, -206860]]]
  hmulB := by decide  
  f := ![![![9528358272, 1916137972, 834267701]], ![![14782587871, 2972755341, 1294308552]], ![![21596221904, 4342966507, 1890885070]]]
  g := ![![![-8994, 12367, -4497], ![-62962, -123664, 112427], ![247333, 142784, -206860]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![364961485940761444901, 73393185013166497042, 31954673736825177792]] ![![-731890, -28106, 49467]]
  ![![9528358272, 1916137972, 834267701]] where
 M := ![![![9528358272, 1916137972, 834267701]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![9528358272, 1916137972, 834267701]] ![![-84316, 12367, -4497]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8697731764568, -200369275518, -238715948607]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![8697731764568, -200369275518, -238715948607]] 
 ![![19, 0, 0], ![0, 19, 0], ![1, 10, 1]] where
  M :=![![![8697731764568, -200369275518, -238715948607], ![-41221165762833, 4038452811695, -886806358323], ![-4662368486310, -6987016912911, 4763236567589]]]
  hmulB := by decide  
  f := ![![![-686314478161496021376058, -138016770024597633723741, -60091149546858615157641]], ![![-10551620112562018459404093, -2121914330531885380227178, -923860711556205224317005]], ![![-6439583196535653036980485, -1294990126787604759824407, -563826014451943561396195]]]
  g := ![![![470339353325, 115094221608, -238715948607], ![-2122861021290, 679290336575, -886806358323], ![-496084476521, -2874704346779, 4763236567589]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [4, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18], [0, 1]]
 g := ![![[17, 5], [1, 7], [7], [1]], ![[0, 14], [0, 12], [7], [1]]]
 h' := ![![[8, 18], [15, 10], [7, 11], [15, 8], [0, 1]], ![[0, 1], [0, 9], [0, 8], [3, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [16, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [4, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![347182, 268667, 153990]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10168, -66907, 153990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-686314478161496021376058, -138016770024597633723741, -60091149546858615157641]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-686314478161496021376058, -138016770024597633723741, -60091149546858615157641]] 
 ![![19, 0, 0], ![18, 1, 0], ![10, 0, 1]] where
  M :=![![![-686314478161496021376058, -138016770024597633723741, -60091149546858615157641], ![-10551620112562018459404093, -2121914330531885380227178, -923860711556205224317005], ![-16149565130395727087212227, -3247652333621039000668212, -1413996009478016808200014]]]
  hmulB := by decide  
  f := ![![![8697731764568, -200369275518, -238715948607]], ![![6070421368389, 22726623809, -272825970171]], ![![4332365745230, -473195245689, 125056688501]]]
  g := ![![![126257835671044607222510, -138016770024597633723741, -60091149546858615157641], ![1941128681714419506729219, -2121914330531885380227178, -923860711556205224317005], ![2970954577345428579306091, -3247652333621039000668212, -1413996009478016808200014]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![8697731764568, -200369275518, -238715948607]] ![![-686314478161496021376058, -138016770024597633723741, -60091149546858615157641]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [22, 1, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 9, 22], [10, 13, 1], [0, 1]]
 g := ![![[17, 18, 9], [10, 12, 6], [15, 4, 1], []], ![[11, 4, 1, 7], [8, 6, 16, 20], [7, 15, 20, 15], [9, 1]], ![[6, 15, 14, 1], [15, 7, 17, 16], [5, 6, 15, 12], [7, 1]]]
 h' := ![![[17, 9, 22], [10, 20, 3], [15, 12, 11], [0, 0, 1], [0, 1]], ![[10, 13, 1], [2, 16, 19], [1, 5, 16], [22, 22, 13], [17, 9, 22]], ![[0, 1], [2, 10, 1], [1, 6, 19], [15, 1, 9], [10, 13, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 5], []]
 b := ![[], [8, 17, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [22, 1, 19, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23460, -12420, -2346]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1020, -540, -102]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [11, 5, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 12, 16], [24, 16, 13], [0, 1]]
 g := ![![[25, 25, 28], [20, 22], [11, 1, 13], [1]], ![[27, 26, 28, 1], [28, 4], [26, 23, 0, 1], [7, 13, 6, 7]], ![[2, 21, 17, 6], [19, 24], [26, 24, 9, 1], [26, 5, 9, 22]]]
 h' := ![![[15, 12, 16], [8, 7, 17], [24, 26, 14], [18, 24, 10], [0, 1]], ![[24, 16, 13], [2, 6, 7], [7, 26, 2], [21, 5, 22], [15, 12, 16]], ![[0, 1], [19, 16, 5], [24, 6, 13], [24, 0, 26], [24, 16, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 20], []]
 b := ![[], [23, 10, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [11, 5, 19, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32193596, 7791952, 2946168]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1110124, 268688, 101592]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44172544734, -8883029780, -3867584141]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-44172544734, -8883029780, -3867584141]] 
 ![![31, 0, 0], ![0, 31, 0], ![16, 1, 1]] where
  M :=![![![-44172544734, -8883029780, -3867584141], ![-679122947671, -136570564471, -59461485817], ![-1039417658896, -209025268375, -91007554073]]]
  hmulB := by decide  
  f := ![![![516032, 14615, -31479]], ![![-5353679, 24734, 211357]], ![![300174, 1124, -13491]]]
  g := ![![![571251662, -161788569, -3867584141], ![8782607271, -2487389634, -59461485817], ![13442038912, -3807023042, -91007554073]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [21, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 30], [0, 1]]
 g := ![![[7, 9], [14, 7], [3, 20], [8, 1]], ![[17, 22], [8, 24], [8, 11], [16, 30]]]
 h' := ![![[8, 30], [16, 28], [30, 21], [18, 12], [0, 1]], ![[0, 1], [23, 3], [12, 10], [21, 19], [8, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [12, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [21, 23, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27991, 36855, 21820]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10359, 485, 21820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![516032, 14615, -31479]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![516032, 14615, -31479]] 
 ![![31, 0, 0], ![26, 1, 0], ![30, 0, 1]] where
  M :=![![![516032, 14615, -31479], ![-5353679, 24734, 211357], ![6402561, -223730, -125914]]]
  hmulB := by decide  
  f := ![![![-44172544734, -8883029780, -3867584141]], ![![-58955132605, -11855785121, -5161892693]], ![![-76277225836, -15339231025, -6678550913]]]
  g := ![![![34852, 14615, -31479], ![-397983, 24734, 211357], ![516031, -223730, -125914]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-44172544734, -8883029780, -3867584141]] ![![516032, 14615, -31479]]
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


lemma PB219I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB219I0 : PrimesBelowBoundCertificateInterval O 1 31 219 where
  m := 11
  g := ![2, 3, 3, 1, 1, 2, 3, 2, 1, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB219I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![343]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![24389]
    · exact ![961, 31]
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
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
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
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I13N0, I13N1, I17N0, I17N1, I17N2, I19N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N0, I5N1], [], [], [I13N0, I13N1], [I17N0, I17N1, I17N2], [I19N1], [], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
