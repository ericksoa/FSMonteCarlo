module MonteCarloSimulation
open System
open Microsoft.FSharp.Collections 

type Property =
  { Zip : string }

type Debtor =
  { FicoScore : int }

//Specifies how principal and interest break down in any given month
//up to maturation of a debt, such as a bond or mortgage.
type AmoritizationTableEntry = 
  { Interest:decimal; 
    Principal:decimal; 
    Remaining:decimal 
  }

//With a given value and balance, equity is the difference between the two
type MonthlyEquityCalculation =
  { PropertyValue : decimal;
    MortgageBalance : decimal;
  }
  with 
  member calc.Equity =
    calc.PropertyValue - calc.MortgageBalance

type Mortgage =
  { Collateral : Property;
    Homeowner : Debtor;
    InterestRate : decimal; 
    Amount : decimal;
    AssessedValueAtOrigination : decimal
    Term : int;
  }
  with
  member m.Payment =
    let J = Convert.ToDouble (m.InterestRate / 12m)
    let P = Convert.ToDouble m.Amount 
    let N = Convert.ToDouble m.Term
    let M p j n = P * ( J / (1.0 - ((1.0 + J) ** (-1.0 * N))))
    let payment = M P J N
    Convert.ToDecimal payment
  member m.Amoritization =    
    let getAmoritizationEntry (month:int) (oldBalance:decimal) (paymentAmount:decimal) =
      let interestRateThisMonth = m.InterestRate
      let interestThisMonth = oldBalance * (interestRateThisMonth / 12m)
      let principalThisMonth = paymentAmount - interestThisMonth
      { 
        Interest = interestThisMonth; 
        Principal = principalThisMonth; 
        Remaining = oldBalance - principalThisMonth }
    let seedMonth = getAmoritizationEntry 1 m.Amount m.Payment
    //Note, scan is like fold (which in turn, is like reduce or C#'s aggregate)
    //  difference is that scan gives you a sequence of intermediate results
    //  which is really useful when you want to produce a sequence
    //  of amoritization table entries
    {2 .. m.Term} |> Seq.scan ( 
      fun prev month -> getAmoritizationEntry month prev.Remaining m.Payment 
    ) seedMonth
  //Note, this tells me what, for a given mortgage combined with
  //  a given appreciation function, what the estimated value of the home
  //  will be in any given month
  member m.EstimatedAssessedValue monthlyAppreciationFunction month =
    {1 .. month} |> Seq.fold ( 
      fun prev month -> (1m + (month |> monthlyAppreciationFunction)) * prev) m.AssessedValueAtOrigination
  //Distribution of generates a set of returns for a given mortgage by application
  //  that takes a mortgage as input and a decimal as output
  member m.GenerateReturnSet sampleSize riskFunction =
    {1 .. sampleSize} |> PSeq.map (fun _ -> riskFunction m)
  //Equity sequence provides a sequence of decimal values that represent
  //  how much equity is in a house, for each month.
  member m.EquitySequence monthlyAppreciationFunction =
    m.Amoritization 
    |> Seq.mapi( fun month amoritizationEntry ->
      {
        PropertyValue = (m.EstimatedAssessedValue monthlyAppreciationFunction month);
        MortgageBalance = amoritizationEntry.Remaining
      }
    )

//Represents a group of mortgages
type MortgagePortfolio =
  { Mortgages : seq<Mortgage>
  }
  with
  //Runs a risk model over the portfolio a given number
  //  of iterations, returns the average return given
  //  that risk model.
  member portfolio.Returns sampleSize riskModel = 
    {1 .. sampleSize}
    |> PSeq.map( fun _ ->
      let capitalInvested,capitalReturned = 
        portfolio.Mortgages
        |> Seq.map( fun m -> m, m.GenerateReturnSet 1 riskModel |> Seq.average )
        |> Seq.fold(
          fun (prevCapitalTotal,prevReturnTotal) (mortgage,retrn) -> 
            (prevCapitalTotal + mortgage.Amount,prevReturnTotal + (mortgage.Amount * retrn))
          ) 
          (0m,0m)
      capitalReturned / capitalInvested
    )
    |> PSeq.average 
    
// A general dice roll used in the simulation
let randomNum() = Convert.ToDecimal((new System.Random(Guid.NewGuid().GetHashCode())).Next(1000000)) / 1000000m

// 
type RealisticModelInputs =
  { BaseForeclosureRate: decimal;
    DistressSaleRate   : decimal;
  }

// in a more realistic model, risk is correlated to a base foreclosure rate
// credit score, and amount of equity you have in a home
let moreRealisticRiskModel (modelInputs:RealisticModelInputs) (mortgage:Mortgage) =
  
  let monthlyAppreciationFunction _ = randomNum() - 0.5m
  let equitySequence = mortgage.EquitySequence monthlyAppreciationFunction
  //credit score of 800 = 0.01 foreclosure risk, 600 = 0.10 risk
  let creditFactor = ((decimal) (700 - mortgage.Homeowner.FicoScore)) / 700m
  let foreclosureHappenedOverMonth() = randomNum() < (modelInputs.BaseForeclosureRate/12m - creditFactor)
  //simulates the risk of foreclosure happening in each month, resulting in a sequence of equity amounts in the lead up
  //to when the foreclosure occurs
  let equitySequenceBeforeForeclosure = 
    equitySequence 
    |> Seq.takeWhile (fun _ -> not (foreclosureHappenedOverMonth()))
  //if the number of sequences before foreclosure is the same as the number of payments, no foreclosure happened
  let noForeclosureHappened = (equitySequenceBeforeForeclosure |> Seq.length) = mortgage.Term
  
  if noForeclosureHappened then
    1.0m //contract fully realized at 100 cents on dollar
  else
    let sequenceBeforeForeclosureLength = equitySequenceBeforeForeclosure |> Seq.length
    //the sequence was before foreclosure.  To calculate return properly, we need the actual month of foreclosure as well
    let foreclosureMonth = 
      match sequenceBeforeForeclosureLength with
      | 0 -> equitySequence |> Seq.head
      | _ -> equitySequence |> Seq.nth( sequenceBeforeForeclosureLength - 1 )
    //combine the foreclosure month with those before it
    let equitySequenceToForeclosure = equitySequenceBeforeForeclosure |> Seq.append ( seq [foreclosureMonth] )
    let distressedEquity = 
      { PropertyValue = foreclosureMonth.PropertyValue * modelInputs.DistressSaleRate; 
        MortgageBalance = foreclosureMonth.MortgageBalance }
    if distressedEquity.Equity > 0m then
      1.0m //there is money left over for the homeowner after foreclosure, contract realized at 100 cents on dollar
    else
      distressedEquity.PropertyValue / distressedEquity.MortgageBalance //percentage of payout on bond after foreclosure

// in a pre bubble model, foreclosure rate was static
// and home prices went up forever
type PreBubbleModelInputs =
  { ForeclosureRate : decimal;
    AppreciationRate: decimal;
    DistressSaleRate: decimal;
  }
     
let preBubbleRiskModel (modelInputs:PreBubbleModelInputs) (mortgage:Mortgage) =

  //in this model, our appreciation function is a straight appreciation rate, and does not consider the month
  let monthlyAppreciationFunction m = modelInputs.AppreciationRate / 12m    

  //sequence of values that represent how much equity is in a given mortgage, which depends on the appreciation model 
  let equitySequence = mortgage.EquitySequence monthlyAppreciationFunction  

  //"roll of the dice" to determine whether a foreclosure happened in a given month
  let foreclosureHappenedOverMonth() = randomNum() < (modelInputs.ForeclosureRate/12m)

  //simulates the risk of foreclosure happening in each month, resulting in a sequence of equity amounts in the lead up
  //to when the foreclosure occurs
  let equitySequenceBeforeForeclosure = 
    equitySequence 
    |> Seq.takeWhile (fun _ -> not (foreclosureHappenedOverMonth()))
  //if the number of sequences before foreclosure is the same as the number of payments, no foreclosure happened
  let noForeclosureHappened = (equitySequenceBeforeForeclosure |> Seq.length) = mortgage.Term
  
  if noForeclosureHappened then
    1.0m //contract fully realized at 100 cents on dollar
  else
    let sequenceBeforeForeclosureLength = equitySequenceBeforeForeclosure |> Seq.length
    //the sequence was before foreclosure.  To calculate return properly, we need the actual month of foreclosure as well
    let foreclosureMonth = 
      match sequenceBeforeForeclosureLength with
      | 0 -> equitySequence |> Seq.head
      | _ -> equitySequence |> Seq.nth( sequenceBeforeForeclosureLength - 1 )
    //combine the foreclosure month with those before it
    let equitySequenceToForeclosure = equitySequenceBeforeForeclosure |> Seq.append ( seq [foreclosureMonth] )
    let distressedEquity = 
      { PropertyValue = foreclosureMonth.PropertyValue * modelInputs.DistressSaleRate; 
        MortgageBalance = foreclosureMonth.MortgageBalance }
    if distressedEquity.Equity > 0m then
      1.0m //there is money left over for the homeowner after foreclosure, contract realized at 100 cents on dollar
    else
      distressedEquity.PropertyValue / distressedEquity.MortgageBalance //percentage of payout on bond after foreclosure

let someFixedRateMortgages = 
  { 
    Mortgages = 
      seq [
        { Collateral = { Zip = "12345" }; 
          Homeowner = { FicoScore = 720 } ; 
          InterestRate = 0.06125m; 
          Amount = 100000m; 
          AssessedValueAtOrigination = 100000m; 
          Term = 360; };
        { Collateral = { Zip = "12345" }; 
          Homeowner = { FicoScore = 700 } ; 
          InterestRate = 0.06125m; 
          Amount = 250000m; 
          AssessedValueAtOrigination = 250000m; 
          Term = 360; };
        { Collateral = { Zip = "12345" }; 
          Homeowner = { FicoScore = 680 } ; 
          InterestRate = 0.06125m; 
          Amount = 1000000m; 
          AssessedValueAtOrigination = 1000000m; 
          Term = 360; };
        { Collateral = { Zip = "12345" }; 
          Homeowner = { FicoScore = 660 } ; 
          InterestRate = 0.06125m; 
          Amount = 275000m; 
          AssessedValueAtOrigination = 275000m; 
          Term = 360; };
        { Collateral = { Zip = "12345" }; 
          Homeowner = { FicoScore = 600 } ; 
          InterestRate = 0.06125m; 
          Amount = 230000m; 
          AssessedValueAtOrigination = 230000m; 
          Term = 360; };
      ];
  }

let foreclosureRates = {1m .. 10m} |> Seq.map (fun x -> x / 100m)
let preBubbleModels = 
  foreclosureRates 
  |> Seq.map 
    (
      fun rate -> 
      rate,
      { 
        ForeclosureRate = rate; 
        AppreciationRate =  -0.1m; 
        DistressSaleRate = 0.75m 
      } |> preBubbleRiskModel 
  )

let moreRealisticForeclosureModels =
  foreclosureRates
  |> Seq.map
    (
      fun rate ->
      rate,
      {
        BaseForeclosureRate = rate;
        DistressSaleRate = 0.70m;
      } |> moreRealisticRiskModel
    )

let sampleSize = 10
let mortgageCount = someFixedRateMortgages.Mortgages |> Seq.length 

type ForeclosureModelResult =
  { ForeclosureRate: decimal;
    ReturnRate: decimal;
  } 

let estimatedPortfolioReturnDistribution = 
  preBubbleModels
  |> PSeq.map( 
    fun (rate,model) -> 
      { 
        ForeclosureRate = rate; 
        ReturnRate = someFixedRateMortgages.Returns sampleSize model 
      } 
  ) 

printf "Distribution of returns given various foreclosure rates\n"
estimatedPortfolioReturnDistribution
  |> Seq.iter ( 
    fun result -> 
      printf "At %d%% annual foreclosure rate, expected return is %d cents on the dollar\n"
        ((int)(result.ForeclosureRate * 100m))
        ((int)(result.ReturnRate * 100m))
  )

printf "Press any key to continue screwing up the economy\n"
Console.ReadKey() |> ignore