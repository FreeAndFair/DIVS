package model.process;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import model.ElectionConstants;
import model.ElectionStatus;
import model.data.Party;
import model.data.computation.CandidateResult;
import model.data.computation.ConstituencyResult;
import model.data.computation.Div;
import model.data.computation.PartyResult;
import model.data.computation.ProvinceResult;
import model.data.computation.draw.StepFiveDraw;
import model.data.computation.draw.StepFourDraw;
import model.data.computation.draw.StepOneDraw;
import model.data.computation.draw.StepSixDraw;
import model.data.computation.draw.StepThreeDraw;
import model.utils.Cmp;
import model.utils.DivsException;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class ElectionResult {

	private int inner_status;
	private List<ConstituencyResult> constituency_results;
	private List<PartyResult> national_results;
	private List<ProvinceResult> province_results;
	private int total_valid_votes, seats_total, total_passing_votes, total_invalid_votes, additional_seats_taken;
	private double quota;

	//@ invariant inner_status == ElectionStatus.BEFORE_COMPUTING || inner_status == ElectionStatus.STEP_1_DONE || inner_status == ElectionStatus.STEP_1_RESOLVED || inner_status == ElectionStatus.THRESHOLD_DETERMINED || inner_status == ElectionStatus.STEP_3_DONE || inner_status == ElectionStatus.STEP_3_RESOLVED || inner_status == ElectionStatus.STEP_4_DONE || inner_status == ElectionStatus.STEP_4_RESOLVED || inner_status == ElectionStatus.STEP_5_DONE || inner_status == ElectionStatus.STEP_5_RESOLVED || inner_status == ElectionStatus.STEP_6_DONE || inner_status == ElectionStatus.STEP_6_RESOLVED;

	/**
	 * Private constructor which ensures that class is singleton
	 */
	//@ post inner_status == ElectionStatus.BEFORE_COMPUTING;
	//@ assignable inner_status;
	public ElectionResult() {
		inner_status = ElectionStatus.BEFORE_COMPUTING;
	}

	/**
	 * @return the inner_status of the election
	 */
	public /*@ pure @*/ int getInnerStatus() {
		return inner_status;
	}

	/**
	 * @return the constituency_results
	 */
	public /*@ pure @*/ List<ConstituencyResult> getConstituencyResults() {
		return constituency_results;
	}

	/**
	 * @return the national_results
	 */
	public /*@ pure @*/ List<PartyResult> getNationalResults() {
		return national_results;
	}

	/**
	 * @return the province_results
	 */
	public /*@ pure @*/ List<ProvinceResult> getProvinceResults() {
		return province_results;
	}

	/**
	 * @return the valid_votes
	 */
	public /*@ pure @*/ int getTotalValidVotes() {
		return total_valid_votes;
	}

	/**
	 * @return the invalid_votes
	 */
	public /*@ pure @*/ int getTotalInvalidVotes() {
		return total_invalid_votes;
	}

	/**
	 * @return the total_passing_votes
	 */
	public /*@ pure @*/ int getTotalPassingVotes() {
		return total_passing_votes;
	}

	/**
	 * @return the seats_total
	 */
	public /*@ pure @*/ int getSeatsTotal() {
		return seats_total;
	}

	/**
	 * @return the quota
	 */
	public /*@ pure @*/ double getQuota() {
		return quota;
	}

	/**
	 * @param const_res List of ConstituencyResult containing accumulated party votes
	 */
	//@ post constituency_results == const_res;
	//@ assignable constituency_results;
	public void setConstituencyResult(
			/*@ non_null @*/ List<ConstituencyResult> const_res) {
		this.constituency_results = const_res;
	}

	/**
	 * @param province_res List of ProvinceResult containing accumulated party votes on province level
	 */
	//@ post province_results == province_res;
	//@ assignable province_results;
	public void setProvinceResult(
			/*@ non_null @*/ List<ProvinceResult> province_res) {
		this.province_results = province_res;
	}
	
	/**
	 * @param national_res List of PartyResult containing accumulated party votes on national level
	 */
	//@ post national_results == national_res;
	//@ assignable national_results;
	public void setNationalResult(
			/*@ non_null @*/ List<PartyResult> national_res) {
		this.national_results = national_res;
	}

	/**
	 * @param invalid_votes the invalid_votes to set
	 */
	//@ pre inv_votes > 0;
	//@ post total_invalid_votes == inv_votes;
	//@ assignable total_invalid_votes;
	public void setTotalInvalidVotes(int inv_votes) {
		this.total_invalid_votes = inv_votes;
	}
	
	/**
	 * Method informs class of total no of votes casted in the election
	 * @param votes Votes
	 */
	//@ pre votes > 0;
	//@ post total_valid_votes == votes;
	//@ assignable total_valid_votes;
	public void setTotalValidVotes(int votes) {
		this.total_valid_votes = votes;
	}

	/**
	 * Step 1:
	 * Allocate constituency seats to parties within constituencies. Note
	 * that after this step there might be more seats taken than there 
	 * should be, and therefore lots must be drawn; i.e. constituency seats
	 * must be pruned 
	 */
	//@ pre inner_status == ElectionStatus.BEFORE_COMPUTING;
	//@ pre constituency_results.size() == ElectionConstants.NO_OF_CONSTITUENCIES; // (1)
	//@ pre \forall int j; 0 <= j && j < constituency_results.size(); constituency_results.get(j).getSeatsTaken() == 0;
	//@ pre \forall int j; 0 <= j && j < constituency_results.size(); \forall int k; 0 <= k && k < constituency_results.get(j).getPartyResult().size(); constituency_results.get(j).getPartyResult().get(k).getConstituencySeats() == 0 && constituency_results.get(j).getPartyResult().get(k).getAdditionalSeats() == 0 && constituency_results.get(j).getPartyResult().get(k).getAdditionalSeatsTaken() == 0;
	//@ pre \forall int j; 0 <= j && j < constituency_results.size(); \forall int k; 0 <= k && k < constituency_results.get(j).getIndependentCandidates().size(); !constituency_results.get(j).getIndependentCandidates().get(k).isElected();
	//@ pre \forall int i; 0 <= i && i < constituency_results.size(); \forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); \exists int n; 0 <= n && n < national_results.size(); constituency_results.get(i).getPartyResult().get(j).getParty().getPartyId() == national_results.get(n).getParty().getPartyId();     
	//@ pre \forall int j; 0 <= j && j < constituency_results.size(); ((\exists int k; 0 <= k && k < constituency_results.get(j).getPartyResult().size(); constituency_results.get(j).getPartyResult().get(k).getTotalVotes() > 0) || (constituency_results.get(j).getElectableIndependentCandidates() >= constituency_results.get(j).getConstituency().getConstituencySeats()));
	//@ post inner_status == ElectionStatus.STEP_1_DONE || inner_status == ElectionStatus.STEP_1_RESOLVED;
	//@ post \forall int j; 0 <= j && j < constituency_results.size(); constituency_results.get(j).getSeatsTaken() >= constituency_results.get(j).getConstituency().getConstituencySeats();
	//@ post (\exists int i; 0 <= i && i < constituency_results.size(); \exists int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(j).isDraw() ==> ((\exists int k; 0 <= k && k < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(k).isDraw() && j != k)) || (\exists int m; 0 <= m && m < constituency_results.get(i).getIndependentCandidates().size(); constituency_results.get(i).getIndependentCandidates().get(m).isDraw()));
	//@ post (\exists int i; 0 <= i && i < constituency_results.size(); \exists int j; 0 <= j && j < constituency_results.get(i).getIndependentCandidates().size(); constituency_results.get(i).getIndependentCandidates().get(j).isDraw() ==> ((\exists int k; 0 <= k && k < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(k).isDraw()) || (\exists int m; 0 <= m && m < constituency_results.get(i).getIndependentCandidates().size(); constituency_results.get(i).getIndependentCandidates().get(m).isDraw() && j != m)));
	//@ post !isStep1Resolved() ==> inner_status == ElectionStatus.STEP_1_DONE;
	//@ post !isStep1Resolved() ==> (\exists int i; 0 <= i && i < constituency_results.size(); (\exists int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(j).isDraw() && (\exists int k; 0 <= k && k < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(j).isDraw() && j != k)));
	//@ post isStep1Resolved() ==> inner_status == ElectionStatus.STEP_1_RESOLVED;
	//@ assignable inner_status, constituency_results;
	public void allocateConstituencySeats() {
		/*
		 * For evert constituency...
		 */
		for (int i = 0; i < constituency_results.size(); i++) {
			/*
			 * Now go through and continue to set all seats of this
			 * constituency by adding to the divisor list - most often one
			 * seat at a time. There might be more seats taken after this 
			 * step, that there are seats allocated, but if so then lots
			 * have to be drawn later. 
			 */
			findSeats(constituency_results.get(i));
		}

		/*
		 * Determine the branching postcondition and
		 * possibly prepare the next step
		 */
		if (!isStep1Resolved()) {
			inner_status = ElectionStatus.STEP_1_DONE;
		} else {
			inner_status = ElectionStatus.STEP_1_RESOLVED;
			this.prepareStepTwo();			
		}
	}

	//@ pre inner_status == ElectionStatus.STEP_1_DONE;
	public List<StepOneDraw> getStepOneDraw() {
		List<StepOneDraw> draws = new ArrayList<StepOneDraw>();
		ConstituencyResult cr;
		PartyResult presc;
		CandidateResult cres;
		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			if (cr.getSeatsTaken() > cr.getConstituency().getConstituencySeats()) {
				StepOneDraw sod = new StepOneDraw(cr);
				for (int j = 0; j < cr.getPartyResult().size(); j++) {
					presc = cr.getPartyResult().get(j);
					if (presc.isDraw()) {
						sod.getParties().add(presc);
					}
				}
				for (int j = 0; j < cr.getIndependentCandidates().size(); j++) {
					cres = cr.getIndependentCandidates().get(j);
					if (cres.isDraw() && cres.isElected()) {
						sod.getCandidates().add(cres);
					}
				}
				draws.add(sod);
			}
		}
		return draws;
	}

	/**
	 * Step 1 (if too many seats are taken in some constituency/ies):
	 * Method is used by Ministry of Interior to register the
	 * result of the lots drawn used to break ties.
	 * 
	 * The arguments passed to this method must be the constituency
	 * where the tie is, and the party that has lost the draw.
	 */
	//@ pre inner_status == ElectionStatus.STEP_1_DONE;
	//@ pre p_cr.getSeatsTaken() > p_cr.getConstituency().getConstituencySeats();
	//@ pre p_pres != null ^ p_cres != null;
	//@ pre (p_pres != null) ==> p_pres.isDraw() && p_pres.getConstituencySeats() > 0;
	//@ pre (p_cres != null) ==> p_cres.isDraw() && p_cres.isElected();
	//@ pre \exists int i; 0 <= i && i < constituency_results.size(); constituency_results.get(i).getConstituency().getConstituencyId() == p_cr.getConstituency().getConstituencyId() && ((\exists int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(j).isDraw() && constituency_results.get(i).getPartyResult().get(j).getParty().getPartyId() != p_pres.getParty().getPartyId()) || (\exists int k; 0 <= k && k < constituency_results.get(i).getIndependentCandidates().size(); constituency_results.get(i).getIndependentCandidates().get(k).isDraw()));
	//@ pre \exists int i; 0 <= i && i < p_cr.getPartyResult().size(); p_pres.getParty().getPartyId() == p_cr.getPartyResult().get(i).getParty().getPartyId();
	//@ post p_cr.getSeatsTaken() == \old(p_cr).getSeatsTaken() - 1;
	//@ post (p_pres != null) ==> !p_pres.isDraw() && p_pres.getConstituencySeats() == \old(p_pres).getConstituencySeats() - 1;
	//@ post (p_cres != null) ==> !p_cres.isDraw() && !p_cres.isElected();
	//@ post isStep1Resolved() ==> inner_status == ElectionStatus.STEP_1_RESOLVED;
	//@ assignable constituency_results, inner_status;
	public void resolveConstituencySeats(
			PartyResult p_pres, CandidateResult p_cres,
			/*@ non_null @*/ ConstituencyResult p_cr) {
		
		ConstituencyResult cr;
		PartyResult pres;
		CandidateResult cres;

		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			if (cr.getConstituency().getConstituencyId() == 
					p_cr.getConstituency().getConstituencyId()) {

				/*
				 * Resolve issue in constituency by either...
				 */
				if (p_pres != null) {
	
					/*
					 * ...taking 1 seat from 1 party
					 */
					for (int j = 0; j < cr.getPartyResult().size(); j++) {
						pres = cr.getPartyResult().get(j);
						if (pres.getParty().getPartyId() == p_pres.getParty().getPartyId()) {
							if (pres.isDraw()) { 
								pres.setDraw(false);
								pres.setConstituencySeats(pres.getConstituencySeats() - 1);
								cr.setSeatsTaken(cr.getSeatsTaken() - 1);
							}
						}
					}
				} else if (p_cres != null) {

					/*
					 * ...taking 1 seat from independent candidate
					 */
					for (int j = 0; j < cr.getIndependentCandidates().size(); j++) {
						cres = cr.getIndependentCandidates().get(j);
						if (cres.getCandidate().getCandidateId() == 
								p_cres.getCandidate().getCandidateId()) {
							cres.setDraw(false);
							cres.setElected(false);
							cr.setSeatsTaken(cr.getSeatsTaken() - 1);
						}
					}
				}
			}
		}
		
		/*
		 * Determine the branching postcondition
		 */
		if (isStep1Resolved()) {
			inner_status = ElectionStatus.STEP_1_RESOLVED;
			this.prepareStepTwo();
		}
		
	}

	/**
	 * Step 2:
	 * For a party to pass the threshold it must pass at least one out of
	 * three tests:
	 *  1) Party must have obtained at least 1 constituency seat
	 *  2) Party must have obtained in two out of three provinces at least 
	 *  as many votes as the average number of valid votes cast in the
	 *  province for each constituency seat
	 *  3) Party must have obtained at least 2.0 percent of the total number
	 *  of valid votes cast in the whole country
	 *  
	 *  It is not certain that at least 1 party will pass the threshold, 
	 *  since if all constituency seats are taken by independent candidates,
	 *  then there is no guarantee that a party will pass.
	 */
	//@ pre inner_status == ElectionStatus.STEP_1_RESOLVED;
	//@ pre province_results.size() == ElectionConstants.NO_OF_PROVINCES;
	//@ pre total_valid_votes > 0;
	//@ pre \forall int i; 0 <= i && i < province_results.size(); \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); \exists int n; 0 <= n && n < national_results.size(); province_results.get(i).getPartyResult().get(j).getParty().getPartyId() == national_results.get(n).getParty().getPartyId();     
	//@ pre \forall int j; 0 <= j && j < constituency_results.size(); constituency_results.get(j).getSeatsTaken() == constituency_results.get(j).getConstituency().getConstituencySeats();
	//@ pre countConstituencySeatsOnNationalLevel() + countIndependentCandidatesElected() == ElectionConstants.CONSTITUENCY_SEATS;
	//@ pre \forall int j; 0 <= j && j < national_results.size(); !national_results.get(j).isThresholdPassed();
	//@ post inner_status == ElectionStatus.THRESHOLD_DETERMINED || inner_status == ElectionStatus.NO_PASSING_PARTIES;
	//@ post \forall int i; 0 <= i && i < national_results.size(); national_results.get(i).getConstituencySeats() > 0 ==> national_results.get(i).isThresholdPassed();
	//@ post \forall int i; 0 <= i && i < national_results.size(); \exists int j; 0 <= j && j < province_results.size(); \exists int k; 0 <= k && k < province_results.get(j).getPartyResult().size(); province_results.get(j).getPartyResult().get(k).getParty().getPartyId() == national_results.get(i).getParty().getPartyId() && province_results.get(j).getPartyResult().get(k).getTotalVotes() >= (int)((double)province_results.get(j).getValidVotes() / (double)province_results.get(j).getProvince().getConstituencySeats()) && \exists int m; 0 <= m && m < province_results.size(); \exists int n; 0 <= n && n < province_results.get(m).getPartyResult().size(); (province_results.get(m).getPartyResult().get(n).getParty().getPartyId() == national_results.get(i).getParty().getPartyId() && province_results.get(m).getPartyResult().get(n).getTotalVotes() >= (int)((double)province_results.get(m).getValidVotes() / (double)province_results.get(m).getProvince().getConstituencySeats()) && i != m);
	//@ post \forall int i; 0 <= i && i < national_results.size(); (double)national_results.get(i).getTotalVotes() / (double)total_valid_votes  >= 2.0 ==> national_results.get(i).isThresholdPassed();
	//@ post \exists int j; 0 <= j && j < national_results.size(); national_results.get(j).isThresholdPassed() ==> inner_status == ElectionStatus.THRESHOLD_DETERMINED;
	//@ post \forall int j; 0 <= j && j < national_results.size(); !national_results.get(j).isThresholdPassed() ==> inner_status == ElectionStatus.NO_PASSING_PARTIES;
	//@ post (countPassingParties() > 0) ==> (quota == (double) total_passing_votes / ((double) ElectionConstants.SEATS_DENMARK - countIndependentCandidatesElected()));
	//@ assignable inner_status, national_results;
	public void determineThreshold() {

		/*
		 * On basis of no of constituency seats, no of votes in provinces
		 * or on national level determine the threshold
		 */
		for (int i = 0; i < national_results.size(); i++) {
			national_results.get(i).setThresholdPassed(
					isThresholdPassed(national_results.get(i))
					);
		}

		/*
		 * The outcome here is most likely that threshold has been 
		 * determined for the parties: passed or not and that at lease
		 * one party passed. If all constituency seats, however, are
		 * allocated to independent candidates, then that is not the
		 * case. Possibly prepare next step. 
		 */
		if (countPassingParties() > 0) {
			inner_status = ElectionStatus.THRESHOLD_DETERMINED;
			this.prepareStepThree();
		} else {
			inner_status = ElectionStatus.NO_PASSING_PARTIES;
		}
	}

	/**
	 * Step 3:
	 * All constituency seats are now allocated and here on basis of result
	 * on national level the total number of seats are computed for each
	 * party (Hare quota). The number of additional seats per party is the 
	 * total number of seats minus the number of constituency seats. If a 
	 * party gets more constituency seats than it should, then the calculation
	 * must be done once more, where the parties that have exactly the right 
	 * number or too many seats are left out. After this step there might be
	 * a need of pruning down the number of seats because two or more parties
	 * have a tie 
	 */
	//@ pre inner_status == ElectionStatus.THRESHOLD_DETERMINED;
	//@ pre \forall int j; 0 <= j && j < national_results.size(); national_results.get(j).getAdditionalSeats() == 0;
	//@ pre \exists int j; 0 <= j && j < national_results.size(); national_results.get(j).isThresholdPassed();
	//@ pre quota > 0;
	//@ post seats_total >= ElectionConstants.SEATS_DENMARK;
	//@ post seats_total <= ElectionConstants.SEATS_DENMARK + countPassingParties() - 1;
	//@ post inner_status == ElectionStatus.STEP_3_DONE || inner_status == ElectionStatus.STEP_3_RESOLVED;
	//@ post (seats_total > ElectionConstants.SEATS_DENMARK) ==> inner_status == ElectionStatus.STEP_3_DONE;
	//@ post (seats_total == ElectionConstants.SEATS_DENMARK) ==> inner_status == ElectionStatus.STEP_3_RESOLVED;
	//@ assignable inner_status, seats_total, national_results;
	public void allocateAdditionalSeatsToParties() {
		/*
		 * First the whole integers are used to determine how many seats 
		 * each party should get...
		 */
		seats_total = countIndependentCandidatesElected();
		this.addIntegers();

		/*
		 * ...and afterwards the fractions are used to determine the rest -
		 * the largest fractions win over the smaller ones
		 */
		boolean[] done = initDones();
		this.breakFractions(done);
		
		/*
		 * Check if any party has got more constituency seats that it 
		 * should according to the no of votes on national level. If 
		 * no party gets more constituency seats than it should then 
		 * the distribution is final. Otherwise the distribution must
		 * be remade
		 */
		if (checkNoOfNegativeAdditionalSeats()) {
			/*
			 * Redo the distribution of additional seats. Now initialize
			 * 'done' so that party with exactly enoug or too many seats 
			 * are left out and 'seats_total' is initialized to the no of 
			 * constituency seats these parties represent 
			 */
			done = initDones();
			seats_total = countIndependentCandidatesElected();
			for (int i = 0; i < national_results.size(); i++) {
				if (national_results.get(i).isThresholdPassed()) {
					if (national_results.get(i).getTotalSeats() > 0 && national_results.get(i).getAdditionalSeats() <= 0) {
						done[i] = true;
						seats_total += national_results.get(i).getConstituencySeats();
					}
				}
			}

			/*
			 * Reset total seat count to the number of constituency seats
			 * (implying that no of additional seats becomes 0) and potential
			 * draws  
			 */
			for (int i = 0; i < national_results.size(); i++) {
				national_results.get(i).setDraw(false);
				national_results.get(i).setTotalSeats(
						national_results.get(i).getConstituencySeats());
			}
			
			/*
			 * As before:
			 * First the whole integers are used to determine how many seats 
			 * each party should get...
			 */
			this.addIntegers();

			/*
			 * ...and afterwards the fractions are used to determine the rest -
			 * the largest fractions win over the smaller ones
			 */
			this.breakFractions(done);

			/*
			 * The law says that it must be checked once more here if some 
			 * parties now have more seats than before, but that is not
			 * necessary, since no party can get more seats the second time
			 * than it got the first time 
			 */
		}

		/*
		 * Determine the branching and possibly preparations for next step
		 */
		if (!isStep3Resolved()) {
			inner_status = ElectionStatus.STEP_3_DONE;
		} else {
			inner_status = ElectionStatus.STEP_3_RESOLVED;
			this.prepareStepFour();
		}
	}
	
	//@ pre inner_status == ElectionStatus.STEP_3_DONE;
	public StepThreeDraw getStepThreeDraw() {
		StepThreeDraw draw = new StepThreeDraw();
		PartyResult presn;
		for (int i = 0; i < national_results.size(); i++) {
			presn = national_results.get(i);
			if (presn.isDraw()) {
				draw.getParties().add(presn);
			}
		}
		return draw;
	}

	/**
	 * Step 3 (if there are too many seats taken):
	 * Method is used by Ministry of Interior to prune down
	 * additional seats per party one by one as a result of
	 * lots being drawn to break ties
	 */
	//@ pre inner_status == ElectionStatus.STEP_3_DONE;
	//@ pre \exists int i; 0 <= i && i < national_results.size(); national_results.get(i).getParty().getPartyId() == p_pres.getParty().getPartyId();
	//@ pre p_pres != null;
	//@ pre p_pres.isDraw();
	//@ pre p_pres.getAdditionalSeats() > 0;
	//@ pre seats_total > ElectionConstants.SEATS_DENMARK;
	//@ post !p_pres.isDraw();
	//@ post p_pres.getAdditionalSeats() == \old(p_pres).getAdditionalSeats() - 1;
	//@ post seats_total == \old(seats_total) - 1;
	//@ post (seats_total == ElectionConstants.SEATS_DENMARK) ==> inner_status == ElectionStatus.STEP_3_RESOLVED;
	//@ assignable seats_total, national_results, inner_status;
	public void resolveAdditionalSeats(PartyResult p_pres) {

		/*
		 * Prune one additional seat from one of the parties
		 */
		PartyResult pres;		
		for (int i = 0; i < national_results.size(); i++) {
			pres = national_results.get(i);
			if (pres.getParty().getPartyId() == p_pres.getParty().getPartyId()) {
				if (pres.isDraw()) {
					pres.setAdditionalSeats(pres.getAdditionalSeats() - 1);
					pres.setDraw(false);
					seats_total--;
					break;
				}
			}
		}

		/*
		 *  Check afterwards if seats taken in all constituency match the number
		 *  of constituency seats belonging to the constituency 
		 */
		if (this.isStep3Resolved()) {
			inner_status = ElectionStatus.STEP_3_RESOLVED;
		}
		if (inner_status == ElectionStatus.STEP_3_RESOLVED) {
			this.prepareStepFour();
		}
	}

	/**
	 * Step 4:
	 * All constituency and additional seats taken at this point. But it is
	 * not clear in which provinces the additional seats should belong. This
	 * method distributes the additional seats into the three electoral
	 * provinces. 
	 * 
	 * There might be ties between parties within provinces or ties between 
	 * provinces. If there are then the inner state afterwards is 'step 4 done'
	 * and not 'step 4 pruned'. The ties can be found by two or more rankings
	 * are equal in the div lists
	 */
	//@ pre inner_status == ElectionStatus.STEP_3_RESOLVED;
	//@ pre seats_total == ElectionConstants.SEATS_DENMARK;
	//@ pre additional_seats_taken == 0;
	//@ pre \forall int j; 0 <= j && j <= province_results.size(); province_results.get(j).getAdditionalSeatsTaken() == 0;
	//@ pre \forall int i; 0 <= i && i <= province_results.size(); \forall int j; 0 <= j && j <= province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeats() == 0;
	//@ pre \forall int i; 0 <= i && i <= province_results.size(); \forall int j; 0 <= j && j <= province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getDivs().size() == province_results.get(i).getPartyResult().get(j).getConstituencySeats();
	//@ post additional_seats_taken <= ElectionConstants.ADDITIONAL_SEATS;
	//@ post isStep4Resolved() ==> \forall int i; 0 <= i && i <= province_results.size(); province_results.get(i).getProvince().getAdditionalSeats() == province_results.get(i).getAdditionalSeatsTaken() && \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() == province_results.get(i).getPartyResult().get(j).getAdditionalSeats();
	//@ post !isStep4Resolved() ==> \exists int i; 0 <= i && i <= province_results.size(); province_results.get(i).getAdditionalSeatsTaken() > province_results.get(i).getProvince().getAdditionalSeats() || \exists int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() > province_results.get(i).getPartyResult().get(j).getAdditionalSeats();
	//@ post isStep4Resolved() ==> inner_status == ElectionStatus.STEP_4_RESOLVED;
	//@ post !isStep4Resolved() ==> inner_status == ElectionStatus.STEP_4_DONE;
	//@ post inner_status == ElectionStatus.STEP_4_DONE || inner_status == ElectionStatus.STEP_4_RESOLVED; 
	//@ assignable inner_status, province_results, additional_seats_taken;
	public void allocateAdditionalSeatsToProvinces() {

		/*
		 * Declarations and initialization of the un-arrested values etc. 
		 */
		PartyResult pres2;
		boolean found;
		
		/*
		 * For parties, that do not run in all provinces allocate
		 * their additional seats first
		 */
		List<PartyResult> special = partiesNotRunningInAllProvinces();
		if (special.size() > 0) {

			/*
			 * Temporarily arrest parties not in the special list
			 */
			for (int i = 0; i < national_results.size(); i++) {
				pres2 = national_results.get(i);
				found = false;
				for (int j = 0; j < special.size(); j++) {
					if (special.get(j).getParty().getPartyId() == 
							pres2.getParty().getPartyId()) {
						found = true; break;
					}
				}
				if (!found) {
					pres2.setAdditionalSeatsTaken(pres2.getAdditionalSeats());
				}
			}

			/*
			 * Allocate the additional seats to the special parties
			 */
			while(additional_seats_taken < ElectionConstants.ADDITIONAL_SEATS 
					&& !tooManyAdditionalSeatsTaken() && !areAllPartiesArrested()) {
				findAdditionalSeats();
			}

			/*
			 * Un-arrest parties not in the special list
			 */
			for (int i = 0; i < national_results.size(); i++) {
				pres2 = national_results.get(i);
				found = false;
				for (int j = 0; j < special.size(); j++) {
					if (special.get(j).getParty().getPartyId() == 
							pres2.getParty().getPartyId()) {
						found = true; break;
					}
				}
				if (!found) {
					pres2.setAdditionalSeatsTaken(0);
				}
			}

		}

		/*
		 * Go through the provinces and parties and determine which 
		 * party should get the next additional seat(s) 
		 */
		while(additional_seats_taken < 
				ElectionConstants.ADDITIONAL_SEATS
					&& !tooManyAdditionalSeatsTaken()) {
			findAdditionalSeats();
		}

		/*
		 * Determine if state will be 'step 4 resolved' 
		 * or current state is preserved
		 */
		if (!this.isStep4Resolved()) {
			inner_status = ElectionStatus.STEP_4_DONE;		
		} else {
			inner_status = ElectionStatus.STEP_4_RESOLVED;		
			prepareStepFive();
		}
	}

	/**
	 * A draw will always involve at least one party result and one
	 * province result. Moreover either there are more than one party
	 * result involved or there are more than one province result
	 * involved; possibly both. The parties and provinces involved in
	 * the draw are all in the lists in the returned object. The lists
	 * are always equal in size since same index places belong 
	 * together 
	 * @return A draw object notifying the caller about the problem
	 */
	//@ pre tooManyAdditionalSeatsTaken();
	//@ post \result.getPartyResults().size() > 1 && \result.getProvinceResults().size() > 1 && \result.getPartyResults().size() == \result.getProvinceResults().size(); 
	public /*@ pure @*/ StepFourDraw getStepFourDraw() {
		StepFourDraw draw;

		/*
		 * Find highest ranking number
		 */
		PartyResult pres;
		ProvinceResult pr;
		Div curr;
		int ranking = -1;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				pres = pr.getPartyResult().get(j);
				for (int k = 0; k < pres.getDivs().size(); k++) {
					curr = pres.getDivs().get(k);
					if (curr.getRanking() > 0 && curr.getRanking() > ranking) {
						ranking = curr.getRanking();
					}
				}
			}
		}
		draw = new StepFourDraw(ranking);

		/*
		 * Locate highest ranking number among the divs
		 */
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				pres = pr.getPartyResult().get(j);
				for (int k = 0; k < pres.getDivs().size(); k++) {
					curr = pres.getDivs().get(k);
					if (curr.getRanking() == ranking) {
						/*
						 * Add party result and province result. Party on index
						 * position i and province on position i represents one
						 * (party, province) pair involved in the draw. 
						 */
						draw.getPartyResults().add(pres);
						draw.getProvinceResults().add(pr);
					}
				}
			}
		}

		/*
		 * Return the draw to the caller 
		 */
		return draw;
	}
	
	//@ normal_behavior
	//@ pre tooManyAdditionalSeatsTaken();
	//@ pre rank > 0 && rank <= ElectionConstants.ADDITIONAL_SEATS;
	//@ pre p_presn != null && p_pr != null; 
	//@ pre \exists int i; 0 <= i && i < national_results.size(); national_results.get(i).getParty().getPartyId() == p_presn.getParty().getPartyId() && p_pr.getAdditionalSeatsTaken() > p_pr.getProvince().getAdditionalSeats() || p_presn.getAdditionalSeatsTaken() > p_presn.getAdditionalSeats();
	//@ post additional_seats_taken < \old(additional_seats_taken);
	//@ post \exists int i; 0 <= i && i < national_results.size(); national_results.get(i).getParty().getPartyId() == p_presn.getParty().getPartyId() && national_results.get(i).getAdditionalSeatsTaken() == \old(p_presn).getAdditionalSeatsTaken() - 1;
	//@ post \exists int i; 0 <= i && i < province_results.size(); province_results.get(i).getProvince().getProvinceId() == p_pr.getProvince().getProvinceId() && province_results.get(i).getAdditionalSeatsTaken() == \old(p_pr).getAdditionalSeatsTaken() - 1;
	//@ post \forall int i; 0 <= i && i < province_results.size(); \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); \forall int k; 0 <= k && k < province_results.get(i).getPartyResult().get(j).getDivs().size(); (province_results.get(i).getProvince().getProvinceId() != p_pr.getProvince().getProvinceId() || province_results.get(i).getPartyResult().get(j).getParty().getPartyId() != p_presn.getParty().getPartyId()) ==> province_results.get(i).getPartyResult().get(j).getDivs().get(k).getRanking() != rank;
	//@ exceptional_behavior
	//@ pre !tooManyAdditionalSeatsTaken() || rank <= 0 || rank > 40 || p_presn == null || p_pr == null || (p_pr.getAdditionalSeatsTaken() <= p_pr.getProvince().getAdditionalSeats() && p_presn.getAdditionalSeatsTaken() <= p_presn.getAdditionalSeats());
	//@ signals (DivsException d) (d instanceof DivsException);
	public void resolveStep4draw(int rank, 
			/*@ non_null @*/ PartyResult p_presn, 
			/*@ non_null @*/ ProvinceResult p_pr) throws DivsException {
		
		/*
		 * Check input
		 */
		if (rank < 0 || rank > ElectionConstants.ADDITIONAL_SEATS) {
			throw new DivsException(DivsException.ILLEGAL_INPUT,
					"The ranking must be between 0 and "+
						ElectionConstants.ADDITIONAL_SEATS);
		}
		PartyResult presn;
		for (int i = 0; i < national_results.size(); i++) {
			presn = national_results.get(i);
			if (presn.getParty().getPartyId() == 
					p_presn.getParty().getPartyId()) {
				if (presn.getAdditionalSeatsTaken() <= 
				 		presn.getAdditionalSeats()) {
					/*
					 * If not the draw doesn't involve the party on
					 * the national level, then it must involve the
					 * province
					 */
					if (p_pr.getAdditionalSeatsTaken() <= p_pr.getProvince().getAdditionalSeats()) {
						throw new DivsException(DivsException.ILLEGAL_INPUT,
								"Party result or province result\n" +
								"must be involved in a draw");
					}
				}
			}
		}
		boolean found = false;
		ProvinceResult pr;
		PartyResult presp;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				presp = pr.getPartyResult().get(j);
				if (presp.getParty().getPartyId() == p_presn.getParty().getPartyId()) {
					if (presp.getDivs().get(
							presp.getDivs().size()-2
							).getRanking() 	==  rank) {
						found = true;
					}
				}
			}
		}
		if (!found) {
			throw new DivsException(DivsException.ILLEGAL_INPUT,
					"The party result involved does not have in a draw");
		}

		/*
		 * Eliminate all others with same ranking so that the
		 * algorithm can continue where the draw came...
		 */
		Div curr;
		for (int i = 0; i < national_results.size(); i++) {
			presn = national_results.get(i);
			for (int j = 0; j < province_results.size(); j++) {
				pr = province_results.get(j);
				for (int k = 0; k < pr.getPartyResult().size(); k++) {
					presp = pr.getPartyResult().get(k);
					if (presn.getParty().getPartyId() == presp.getParty().getPartyId()) {
						for (int d = 0; d < presp.getDivs().size(); d++) {
							curr = presp.getDivs().get(d);
							if (curr.getRanking() == rank && 
									(presp.getParty().getPartyId() != 
										p_presn.getParty().getPartyId() || 
									pr.getProvince().getProvinceId() != 
										p_pr.getProvince().getProvinceId())) {
								/*
								 * Eliminate one additional seat by
								 * a) set ranking to 0
								 * b) removing the last div
								 * c) subtract 1 additional seat from party on 
								 * the national level
								 * d) subtract 1 additional seat from party on
								 * provinve level
								 * e) subtract 1 additional seat from province
								 * f) update additional_seats_taken
								 */
								curr.setRanking(0); // a)
								presp.getDivs().remove(presp.getDivs().size()-1); // b)
								presn.setAdditionalSeatsTaken(
										presn.getAdditionalSeatsTaken() - 1); // c)
								presp.setAdditionalSeats(
										presp.getAdditionalSeats() - 1); // d)
								pr.setAdditionalSeatsTaken(pr.getAdditionalSeatsTaken()-1); // e)
								additional_seats_taken -= 1; // f)
							}
						}
					}
				}
			}
		}

		/*
		 * Determine if resolving the draw resolved 
		 * computation step 4
		 */
		if (this.isStep4Resolved()) {
			inner_status = ElectionStatus.STEP_4_RESOLVED;		
			prepareStepFive();
		}
	}
	
	/**
	 * Step 5:
	 * All additional seats are now distributed between the electoral
	 * provinces, but it is not clear which constituencies should the
	 * seats mentioned should belong. This method distributes these
	 * seats among the constituencies.
	 * 
	 * There might be ties between constituencies. If there are then 
	 * the inner state afterwards is 'step 5 done' and not 'step 5 
	 * pruned'. The ties can be found by two or more rankings are equal 
	 * in the div lists.
	 */
	//@ pre inner_status == ElectionStatus.STEP_4_RESOLVED;
	//@ pre \forall int i; 0 <= i && i < constituency_results.size(); \forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); (isThresholdPassed(constituency_results.get(i).getPartyResult().get(j).getParty())) ==> (constituency_results.get(i).getPartyResult().get(j).getMethod() == ElectionConstants.DANISH_METHOD && constituency_results.get(i).getPartyResult().get(j).getAdditionalSeats() == 0 && constituency_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() == 0 && constituency_results.get(i).getPartyResult().get(j).getDivs().size() == (constituency_results.get(i).getPartyResult().get(j).getConstituencySeats() + 1)); 
	//@ pre \forall int i; 0 <= i && i < province_results.size(); \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() == 0; 
	//@ post inner_status == ElectionStatus.STEP_5_DONE || inner_status == ElectionStatus.STEP_5_RESOLVED;
	//@ post \forall int i; 0 <= i && i < province_results.size(); \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); (isThresholdPassed(constituency_results.get(i).getPartyResult().get(j).getParty())) ==> (province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() >= province_results.get(i).getPartyResult().get(j).getAdditionalSeats()); 
	//@ post !isStep5Resolved() ==> inner_status == ElectionStatus.STEP_5_DONE; 
	//@ post isStep5Resolved() ==> inner_status == ElectionStatus.STEP_5_RESOLVED; 
	//@ post (!isStep5Resolved()) ==> (\exists int i; 0 <= i && i < province_results.size(); \exists int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() > province_results.get(i).getPartyResult().get(j).getAdditionalSeats()); 
	//@ post (isStep5Resolved()) ==> (\forall int i; 0 <= i && i < province_results.size(); \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() == province_results.get(i).getPartyResult().get(j).getAdditionalSeats()); 
	//@ assignable inner_status, constituency_results;
	public void allocateAdditionalSeatsToConstituencies() {
		PartyResult presn;
		ProvinceResult pr;
		ConstituencyResult cr;
		PartyResult presp, presc;
		Div curr;
		double highest;
		int ranking, count; 

		/*
		 * For all passing party in each province create divs according
		 * to constituency seats already taken + 1. In the constituency_results
		 * change the divisor method to the 'Danish method'
		 */
		for (int i = 0; i < national_results.size(); i++) {
			presn = national_results.get(i);
			if (isThresholdPassed(presn)) {
				for (int j = 0; j < province_results.size(); j++) {
					pr = province_results.get(j);

					/*
					 * Count no of additional seats in this province and then
					 * initialize the div list of each party in each constituency
					 * within a province
					 */
					for (int p = 0; p < pr.getPartyResult().size(); p++) {
						presp = pr.getPartyResult().get(p);
						if (presp.getParty().getPartyId() == presn.getParty().getPartyId()) {

							/*
							 * For every party in every province make sure that all
							 * additional seats are allocated to the constituencies.
							 * Also give the "winning divs" a ranking
							 */
							ranking = 1;
							while(presp.getAdditionalSeatsTaken() < presp.getAdditionalSeats()) {
								highest = -1;
								/*
								 * Find the highest value for each constituency within the province
								 */
								for (int k = 0; k < constituency_results.size(); k++) {
									cr = constituency_results.get(k);
									if (cr.getConstituency().getProvince().getProvinceId() 
															== pr.getProvince().getProvinceId()) {
										for (int m = 0; m < cr.getPartyResult().size(); m++) {
											presc = cr.getPartyResult().get(m);
											/*
											 * Party id must match party id in outermost for-loop
											 */
											if (presc.getParty().getPartyId() == presn.getParty().getPartyId()) {
												curr = presc.getDivs().get(presc.getDivs().size()-1);
												if (curr.getQuotient() > highest) {
													highest = curr.getQuotient();
												}
											}
										}								
									}							
								}

								/*
								 * Locate the highest value again
								 */
								count = 0;
								for (int k = 0; k < constituency_results.size(); k++) {
									cr = constituency_results.get(k);
									if (cr.getConstituency().getProvince().getProvinceId() 
													== pr.getProvince().getProvinceId()) {
										for (int m = 0; m < cr.getPartyResult().size(); m++) {
											presc = cr.getPartyResult().get(m);
											if (presc.getParty().getPartyId() == presn.getParty().getPartyId()) {
												curr = presc.getDivs().get(presc.getDivs().size()-1);
												if (curr.getQuotient() == highest) {
													count++;
													presp.setAdditionalSeatsTaken(presp.getAdditionalSeatsTaken() + 1);
													curr.setRanking(ranking);
													presc.addOneToDivList();
													presc.setAdditionalSeats(presc.getAdditionalSeats() + 1);
													/*
													 * Additional seats taken on constituency level:
													 * presc.getAdditionalSeatsTaken()
													 * ...is never used
													 */
												}
											}
										}								
									}
								}

								/*
								 * Accumulate the ranking...
								 */
								ranking += count;
							}
						}
					}
				}
			}
		}

		/*
		 * Determine post condition and prepare next step
		 */
		if (!this.isStep5Resolved()) {
			inner_status = ElectionStatus.STEP_5_DONE;		
		} else {
			inner_status = ElectionStatus.STEP_5_RESOLVED;		
			this.prepareStepSix();
		}
	}

	//@ pre inner_status == ElectionStatus.STEP_5_DONE;
	//@ post \result != null;
	public List<StepFiveDraw> getStepFiveDraw() {
		List<StepFiveDraw> draws = new ArrayList<StepFiveDraw>();
		ProvinceResult pr;
		PartyResult presp, presc;
		ConstituencyResult cr;
		Div curr;
		int highest;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				presp = pr.getPartyResult().get(j);
				if (presp.getAdditionalSeatsTaken() > presp.getAdditionalSeats()) {
					highest = -1;
					/*
					 * Locate highest ranking among the divs of the 
					 * party on the constituency level
					 */
					for (int c = 0; c < constituency_results.size(); c++) {
						cr = constituency_results.get(c);
						if (cr.getConstituency()
								.getProvince().getProvinceId() == 
									pr.getProvince().getProvinceId()) {
							for (int k = 0; k < cr.getPartyResult().size(); k++) {
								presc = cr.getPartyResult().get(k);
								if (presp.getParty().getPartyId() == 
										presc.getParty().getPartyId()) {
									for (int m = 0; m < presc.getDivs().size(); m++) {
										curr = presc.getDivs().get(m);
										if (curr.getRanking() > 0 && 
												curr.getRanking() > highest) {
											highest = curr.getRanking();
										}
									}
								}
							}
						}
					}
					StepFiveDraw sfd = new StepFiveDraw(
							highest, presp, pr);
					for (int c = 0; c < constituency_results.size(); c++) {
						cr = constituency_results.get(c);
						if (cr.getConstituency()
								.getProvince().getProvinceId() == 
									pr.getProvince().getProvinceId()) {
							for (int k = 0; k < cr.getPartyResult().size(); k++) {
								presc = cr.getPartyResult().get(k);
								if (presp.getParty().getPartyId() == 
										presc.getParty().getPartyId()) {
									for (int m = 0; m < presc.getDivs().size(); m++) {
										curr = presc.getDivs().get(m);
										if (curr.getRanking() == highest) {
											sfd.getConstituencies().add(cr);
										}
									}
								}
							}
						}
					}
					draws.add(sfd);
				}
			}
		}		
		return draws;
	}

	/**
	 * Step 5 (if there are ties between a party's fractions in different constituencies):
	 * Method gives a certain party in a certain constituency a certain ranking, and 
	 * others with the same ranking are pushed one step down. If the pushed down party 
	 * should not get a seat then it is eliminated.
	 * 
	 * There is a need to program defensively here, since wrong input might ruin
	 * the consistency. Therefore the method has two sets of pre- and post-
	 * conditions. The normal behavior is when ranking is greater than 0, a div
	 * in div list in p_vp has the exact same ranking, and p_vp must be
	 * in the party_result list in p_cr. Input that doesn't fulfill mentioned
	 * criteria causes exceptional behaviour. 
	 * @param ranking The ranking that the party has won by drawing lots
	 * @param vp The (votes) party
	 * @param cr The constituency (result)
	 */
	//@ normal_behavior   
	//@ pre inner_status == ElectionStatus.STEP_5_DONE;
	//@ pre ranking > 0;
	//@ pre \exists int i; 0 <= i && i < p_cr.getPartyResult().size(); p_pres.getParty().getPartyId() == p_cr.getPartyResult().get(i).getParty().getPartyId();
	//@ pre \exists int i; 0 <= i && i < p_pres.getDivs().size(); p_pres.getDivs().get(i).getRanking() == ranking; 
	//@ pre \exists int i; 0 <= i && i < province_results.size(); province_results.get(i).getProvince().getProvinceId() == p_cr.getConstituency().getProvince().getProvinceId() && \exists int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getParty().getPartyId() == p_pres.getParty().getPartyId() && province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() > province_results.get(i).getPartyResult().get(j).getAdditionalSeats();
	//@ pre \exists int i; 0 <= i && i < province_results.size(); \exists int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() > province_results.get(i).getPartyResult().get(j).getAdditionalSeats(); 
	//@ post !isStep5Resolved() ==> inner_status == ElectionStatus.STEP_5_DONE; 
	//@ post isStep5Resolved() ==> inner_status == ElectionStatus.STEP_5_RESOLVED; 
	//@ post (!isStep5Resolved()) ==> (\exists int i; 0 <= i && i < province_results.size(); \exists int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() > province_results.get(i).getPartyResult().get(j).getAdditionalSeats()); 
	//@ post (isStep5Resolved()) ==> (\forall int i; 0 <= i && i < province_results.size(); \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() == province_results.get(i).getPartyResult().get(j).getAdditionalSeats()); 
	//@ assignable constituency_results, inner_status;
	//@ exceptional_behavior
	//@ pre inner_status != ElectionStatus.STEP_5_DONE || ranking <= 0 || (\forall int i; 0 <= i && i < p_cr.getPartyResult().size(); p_pres.getParty().getPartyId() != p_cr.getPartyResult().get(i).getParty().getPartyId()) || (\forall int i; 0 <= i && i < p_cr.getPartyResult().size(); \forall int j; 0 <= j && j < p_cr.getPartyResult().get(i).getDivs().size(); p_cr.getPartyResult().get(i).getParty().getPartyId() != p_pres.getParty().getPartyId() ==> p_cr.getPartyResult().get(i).getDivs().get(j).getRanking() != ranking) || \forall int i; 0 <= i && i < p_cr.getPartyResult().size(); p_pres.getParty().getPartyId() != p_cr.getPartyResult().get(i).getParty().getPartyId() ==> (\forall int j; 0 <= j && j < p_cr.getPartyResult().get(i).getDivs().size(); p_cr.getPartyResult().get(j).getDivs().get(j).getRanking() != ranking);
	//@ signals (DivsException d) (d instanceof DivsException);
	public void resolveConstituencyResult(int ranking, 
			/*@ non_null @*/ PartyResult p_pres, 
			/*@ non_null @*/ ConstituencyResult p_cr) throws DivsException {
		
		PartyResult presn;
		ProvinceResult pr;
		ConstituencyResult cr;
		PartyResult presp, presc;
		Div curr;

		/*
		 * Method throws an exception if and when 1 one the following is true: 
		 * a) ranking is zero or less
		 * b) party does not exist in the party_result list of constituency result
		 * c) no div of others parties has the ranking.
		 * If all tests are ok then continue 
		 */
		if (ranking <= 0) {
			throw new DivsException(DivsException.ILLEGAL_INPUT, 
					"Ranking must be larger than 0");
		}
		boolean found = false;
		for (int i = 0; i < p_cr.getPartyResult().size(); i++) {
			presc = p_cr.getPartyResult().get(i);
			if (presc.getParty().getPartyId() == p_pres.getParty().getPartyId()) {
				found = true; break;
			}
		}
		if (!found) {
			throw new DivsException(DivsException.ILLEGAL_INPUT, 
					"'p_vp' must be an element of the party_result list in 'p_cr'");
		}
		found = false;
		outer: for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			if (cr.getConstituency().getConstituencyId() != 
					p_cr.getConstituency().getConstituencyId()
				&& cr.getConstituency().getProvince().getProvinceId() ==
					p_cr.getConstituency().getProvince().getProvinceId()) {
				for (int j = 0; j < cr.getPartyResult().size(); j++) {
					presc = cr.getPartyResult().get(j);
					if (presc.getParty().getPartyId() == 
							p_pres.getParty().getPartyId()) {
						for (int d = 0; d < presc.getDivs().size(); d++) {
							curr = presc.getDivs().get(d);
							if (curr.getRanking() == ranking) {
								found = true;
								for (int pp = 0; pp < province_results.size(); pp++) {
									pr = province_results.get(pp);
									if (pr.getProvince().getProvinceId() == 
										p_cr.getConstituency()
										.getProvince().getProvinceId()) {
										for (int ppp = 0; ppp < pr.getPartyResult().size(); ppp++) {
											presp = pr.getPartyResult().get(ppp);
											if (presc.getParty().getPartyId() == 
													presp.getParty().getPartyId()) {
												if (presp.getAdditionalSeatsTaken() <= presp.getAdditionalSeats()) {
													throw new DivsException(DivsException.ILLEGAL_INPUT, 
														"Party has no issues to resolve on province level");
												}
												break outer;												
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		if (!found) {
			throw new DivsException(DivsException.ILLEGAL_INPUT, 
					"There must be more than one div with the same ranking ("+ranking+")");
		}
		
		/*
		 * For each party passing the threshold...
		 */
		for (int i = 0; i < national_results.size(); i++) {
			presn = national_results.get(i);
			if (presn.isThresholdPassed()) {
				for (int p = 0; p < province_results.size(); p++) {
					pr = province_results.get(p);
					if (pr.getProvince().getProvinceId() == 
							p_cr.getConstituency().getProvince().getProvinceId()) {
						/*
						 * Count the additional seats that the party has
						 * won in the province 
						 */
						for (int n = 0; n < pr.getPartyResult().size(); n++) {
							presp = pr.getPartyResult().get(n);
							if (presp.getParty().getPartyId() == presn.getParty().getPartyId()) {
								for (int j = 0; j < constituency_results.size(); j++) {
									cr = constituency_results.get(j);
									if (cr.getConstituency().getProvince().getProvinceId() == 
											pr.getProvince().getProvinceId()) {
										for (int k = 0; k < cr.getPartyResult().size(); k++) {
											presc = cr.getPartyResult().get(k);
											if (presc.getParty().getPartyId() == presn.getParty().getPartyId()) {

												/*
												 * Go through the list of divs... 
												 */
												for (int d = 0; d < presc.getDivs().size(); d++) {
													curr = presc.getDivs().get(d);

													/*
													 * ...and find the divs with the ranking number
													 * that we are looking for, and whos party or
													 * province are not the ones that we'll keep
													 */
													if (curr.getRanking() == ranking && 
															p_cr.getConstituency().getConstituencyId() != 
																cr.getConstituency().getConstituencyId()) {
														/*
														 * Push ranking of a constituency one down...
														 */
														curr.setRanking(curr.getRanking()+1);
														if (curr.getRanking() > presp.getAdditionalSeats()) {
															/*
															 * ...but if ranking is higher than the
															 * number of additional seats, then the
															 * constituency is eliminated; i.e. 1
															 * additional seat is take from the 
															 * constituency.
															 */
															curr.setRanking(0);
															presp.setAdditionalSeatsTaken(presp.getAdditionalSeatsTaken() - 1);
															presc.setAdditionalSeats(presc.getAdditionalSeats()-1);
														}
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}

		/*
		 * Determine state and prepare next step
		 */
		if (!this.isStep5Resolved()) {
			inner_status = ElectionStatus.STEP_5_DONE;		
		} else {
			inner_status = ElectionStatus.STEP_5_RESOLVED;		
			this.prepareStepSix();
		}
	}

	/**
	 * Step 6:
	 * Method determins which candidates are elected to the Folketing. The
	 * result might be that too many candidates are selected, but then some
	 * pruning needs to be done
	 */
	//@ pre inner_status == ElectionStatus.STEP_5_RESOLVED;
	//@ pre \forall int i; 0 <= i && i < constituency_results.size(); \forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); \forall int k; 1 <= k && k < constituency_results.get(i).getPartyResult().get(j).getCandidateResults().size(); constituency_results.get(i).getPartyResult().get(j).getCandidateResults().get(k).getTotalVotes() <= constituency_results.get(i).getPartyResult().get(j).getCandidateResults().get(k-1).getTotalVotes(); //not in BON
	//@ pre \forall int i; 0 <= i && i < constituency_results.size(); \forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(j).getNoOfElected() == 0;
	//@ pre \forall int i; 0 <= i && i < constituency_results.size(); \forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(j).getTotalSeats() <= constituency_results.get(i).getPartyResult().get(j).getCandidateResults().size();
	//@ post inner_status == ElectionStatus.STEP_6_DONE || inner_status == ElectionStatus.STEP_6_RESOLVED;
	//@ post \forall int i; 0 <= i && i < constituency_results.size(); (\forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(j).getNoOfElected() >= constituency_results.get(i).getPartyResult().get(j).getTotalSeats());
	//@ post !isStep6Resolved() ==> inner_status == ElectionStatus.STEP_6_DONE;
	//@ post isStep6Resolved() ==> inner_status == ElectionStatus.STEP_6_RESOLVED;
	//@ assignable inner_status, constituency_results;
	public void selectCandidates() {
		ConstituencyResult cr;
		PartyResult pres;
		CandidateResult cres;

		/*
		 * For every constituency...
		 */
		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			for (int j = 0; j < cr.getPartyResult().size(); j++) {
				pres = cr.getPartyResult().get(j);

				/*
				 * Set elected for each elected candidate 
				 */
				int tmp_votes = -1;
				for (int k = 0; k < pres.getCandidateResults().size(); k++) {
					cres = pres.getCandidateResults().get(k);
					if (k+1 <= pres.getTotalSeats()) {
						cres.setElected(true);
						pres.setNoOfElected(pres.getNoOfElected() + 1);
						tmp_votes = cres.getTotalVotes();
					} else {
						if (tmp_votes == cres.getTotalVotes()) {
							cres.setElected(true);
							pres.setNoOfElected(pres.getNoOfElected() + 1);
						} else {
							tmp_votes = -1;
						}
					}
				}
			}
		}
		
		/*
		 * Determine the status...
		 */
		if (this.isStep6Resolved()) {
			inner_status = ElectionStatus.STEP_6_RESOLVED;
		} else {
			inner_status = ElectionStatus.STEP_6_DONE;
		}
	}

	//@ pre inner_status == ElectionStatus.STEP_6_DONE;
	public List<StepSixDraw> getStepSixDraw() {
		List<StepSixDraw> draws = new ArrayList<StepSixDraw>();
		ConstituencyResult cr;
		PartyResult presc;
		CandidateResult cres;
		int save;
		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			for (int j = 0; j < cr.getPartyResult().size(); j++) {
				presc = cr.getPartyResult().get(j);
				if (presc.getNoOfElected() > presc.getTotalSeats()) {
					save = -1;
					StepSixDraw ssd = new StepSixDraw(cr, presc);
					for (int k = presc.getCandidateResults().size()-1; k >= 0; k--) {
						cres = presc.getCandidateResults().get(k);
						if (cres.isElected()) {
							if (save < 0) {
								save = cres.getTotalVotes();
							}
							if (cres.getTotalVotes() == save) {
								ssd.getCandidates().add(cres);
							}
						}
					}
					draws.add(ssd);
				}
			}
		}
		return draws;
	}

	/**
	 * Step 6 (if there are too many candidates elected):
	 * Method is used by Ministry of Interior to break ties between elected 
	 * candidates of a party within a constituency
	 * @param cr The constituency result where the party result resides 
	 * @param pr The party result where the candidate result resides
	 * @param vp The candidate result 
	 */
	//@ normal_behavior
	//@ pre inner_status == ElectionStatus.STEP_6_DONE;
	//@ pre p_cres.isElected();
	//@ pre p_pres.getNoOfElected() > p_pres.getTotalSeats();
	//@ pre \exists int i; 0 <= i && i < p_cr.getPartyResult().size(); p_cr.getPartyResult().get(i).getParty().getPartyId() == p_pres.getParty().getPartyId();
	//@ pre \exists int i; 0 <= i && i < p_pres.getCandidateResults().size(); p_pres.getCandidateResults().get(i).getCandidate().getCandidateId() == p_cres.getCandidate().getCandidateId();
	//@ post !p_cres.isElected();
	//@ post isStep6Resolved() ==> inner_status == ElectionStatus.STEP_6_RESOLVED;
	//@ assignable inner_status, constituency_results;
	//@ exceptional_behavior
	//@ pre !p_cres.isElected() || p_pres.getNoOfElected() <= p_pres.getTotalSeats() || \forall int i; 0 <= i && i < p_cr.getPartyResult().size(); p_cr.getPartyResult().get(i).getParty().getPartyId() != p_pres.getParty().getPartyId(); //|| \forall int j; 0 <= j && j < p_pres.getCandidateResults().size(); p_pres.getCandidateResults().get(j).getCandidate().getCandidateId() != p_cres.getCandidate().getCandidateId();
	//@ signals (DivsException d) (d instanceof DivsException);
	public void resolveCandidates(
			/*@ non_null @*/ ConstituencyResult p_cr, 
			/*@ non_null @*/ PartyResult p_pres, 
			/*@ non_null @*/ CandidateResult p_cres) throws DivsException {
		
		ConstituencyResult cr;
		PartyResult pres;
		CandidateResult cres;
		
		/*
		 * Method throws an exception if and when 1 one the following is true: 
		 * a) there is no issue to resolve for the party
		 * b) candidate isn't elected
		 * c) relationship between candidate, party, and constituency isn't ok
		 */
		if (p_pres.getNoOfElected() <= p_pres.getTotalSeats()) {
			throw new DivsException(DivsException.ILLEGAL_INPUT, 
					"Party must have more elected candidates than " +
					"seats or else there is no draw to resolve");
		}
		if (!p_cres.isElected()) {
			throw new DivsException(DivsException.ILLEGAL_INPUT, 
				"Candidate must be elected");
		}
		boolean party_found = false, candidate_found = false;
		for (int i = 0; i < p_cr.getPartyResult().size(); i++) {
			pres = p_cr.getPartyResult().get(i);
			if (pres.getParty().getPartyId() == 
					p_pres.getParty().getPartyId()) {
				party_found = true;
				break;
			}
		}
		if (!party_found) {
			throw new DivsException(DivsException.ILLEGAL_INPUT, 
					"'p_pres' must be an element of the party_result list in 'p_cr'");
		}
		for (int i = 0; i < p_pres.getCandidateResults().size(); i++) {
			cres = p_pres.getCandidateResults().get(i);
			if (cres.getCandidate().getCandidateId() == 
					p_cres.getCandidate().getCandidateId()) {
				candidate_found = true;
				break;
			}
		}
		if (!candidate_found) {
			throw new DivsException(DivsException.ILLEGAL_INPUT, 
					"'p_cres' must be an element of the cand_result list in 'p_pres'");
		}

		/*
		 * Find candidate among candidates for party among 
		 * parties in constituency...
		 */
		outer: for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			if (cr.getConstituency().getConstituencyId() == 
					p_cr.getConstituency().getConstituencyId()) {
				for (int j = 0; j < cr.getPartyResult().size(); j++) {
					pres = cr.getPartyResult().get(j);
					if (pres.getParty().getPartyId() == 
							p_pres.getParty().getPartyId()) {
						for (int k = pres.getCandidateResults().size()-1; k >= 0; k--) {
							cres = pres.getCandidateResults().get(k);
							if (cres.getCandidate().getCandidateId() == 
									p_cres.getCandidate().getCandidateId()) {
								/*
								 * Un-elect candidate and decrement no 
								 * of elected 
								 */
								cres.setElected(false);
								pres.setNoOfElected(pres.getNoOfElected()-1);

								/*
								 * Sort list of candidates again since the 
								 * elected candidates must precede unelected
								 */
								Collections.sort(pres.getCandidateResults(), new Cmp());

								/*
								 * Break outer loop, since the candidate was found
								 */
								break outer;
							}
						}
					}
				}
			}
		}

		/*
		 * Determine the status...
		 */
		if (isStep6Resolved()) {
			inner_status = ElectionStatus.STEP_6_RESOLVED;
		}
	}

	/**
	 * After step 2 this method determines if any additional seats should be 
	 * distributed. According to §77 stk. 1 only parties passing the threshold 
	 * can get a share of the additional seats. This means that if all 135 
	 * constituency seats are allocated to independent candidates, then no 
	 * additional seats are allocated
	 */
	//@ post \result >= 0;
	//@ post \result <= ElectionConstants.CONSTITUENCY_SEATS; 
	public /*@ pure @*/ int countIndependentCandidatesElected() {
		int retval = 0;
		ConstituencyResult cr;
		CandidateResult cres;
		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			for (int j = 0; j < cr.getIndependentCandidates().size(); j++) {
				cres = cr.getIndependentCandidates().get(j);
				if (cres.isElected()) {
					retval++;
				}
			}
		}
		return retval;
	}
		
	/**
	 * Update result on national level with regards on how many
	 * constituency seats each party has got. This must be done 
	 * after the resolving and before the threshold is computed!
	 */
	//@ pre \forall int j; 0 <= j && j < national_results.size(); national_results.get(j).getConstituencySeats() == 0; 
	//@ pre national_results.size() > 0;
	//@ post countConstituencySeats() == ElectionConstants.CONSTITUENCY_SEATS;
	private void prepareStepTwo () {
		ConstituencyResult cr;
		PartyResult pres;
		PartyResult presp;

		/*
		 * Initialize...
		 */
		for (int i = 0; i < national_results.size(); i++) {
			pres = national_results.get(i);
			pres.setConstituencySeats(0);
			pres.setTotalSeats(0);
			pres.setAdditionalSeats(0);
		}

		/*
		 * For every constituency...
		 */
		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);

			/*
			 * ...check every votes party for constituency seats taken...
			 */
			for (int j = 0; j < cr.getPartyResult().size(); j++) {
				presp = cr.getPartyResult().get(j);
				pres = locatePartyResultOnNationalLevel(presp);

				/*
				 * ...and accumulate constituency seats pr. party
				 */
				pres.setConstituencySeats(pres.getConstituencySeats()
						+ presp.getConstituencySeats());
			}
		}
	}

	/**
	 * Determine total number of passing votes: i.e. total number
	 * of votes casted for parties passing the threshold. Also 
	 * determine the quota
	 */
	//@ pre \exists int j; 0 <= j && j < national_results.size(); national_results.get(j).isThresholdPassed();
	//@ pre countIndependentCandidatesElected() >= 0 && countIndependentCandidatesElected() < ElectionConstants.CONSTITUENCY_SEATS;
	//@ post total_passing_votes > 0;
	//@ post quota == (double) total_passing_votes / ((double) ElectionConstants.SEATS_DENMARK - countIndependentCandidatesElected());
	//@ assignable quota, total_passing_votes;
	private void prepareStepThree () {

		/*
		 * Sum the votes for all passing parties...
		 */
		this.total_passing_votes = 0;
		for (int i = 0; i < national_results.size(); i++) {
			if (national_results.get(i).isThresholdPassed()) {
				this.total_passing_votes += national_results.get(i).getTotalVotes();
			}
		}

		/*
		 * Determine the quota...
		 */
		this.quota = (double) total_passing_votes / 
						((double) ElectionConstants.SEATS_DENMARK - 
								countIndependentCandidatesElected());
	}

	/**
	 * Update no of constituency seats per party per province
	 */
	//@ pre province_results.size() == ElectionConstants.NO_OF_PROVINCES;
	//@ pre \forall int j; 0 <= j && j <= province_results.size(); (\forall int k; 0 <= k && k <= province_results.get(j).getPartyResult().size(); province_results.get(j).getPartyResult().get(k).getConstituencySeats() == 0 && province_results.get(j).getPartyResult().get(k).getAdditionalSeats() == 0);  
	//@ post \forall int j; 0 <= j && j <= province_results.size(); (\exists int k; 0 <= k && k <= province_results.get(j).getPartyResult().size(); province_results.get(j).getPartyResult().get(k).getConstituencySeats() > 0 || province_results.get(j).getPartyResult().get(k).getAdditionalSeats() > 0);
	//@ assignable province_results, additional_seats_taken; 
	private void prepareStepFour() {
		ProvinceResult pr;
		ConstituencyResult cr;
		PartyResult presp, presc;

		/*
		 * Set it to whatever the constituencies got of
		 * constituency seats
		 */
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int p = 0; p < pr.getPartyResult().size(); p++) {
				presp = pr.getPartyResult().get(p);
				presp.setAdditionalSeats(0);
				presp.setConstituencySeats(0);
				for (int j = 0; j < constituency_results.size(); j++) {
					cr = constituency_results.get(j);
					if (pr.getProvince().getProvinceId() == 
							cr.getConstituency().getProvince().getProvinceId()) {
						for (int k = 0; k < cr.getPartyResult().size(); k++) {
							presc = cr.getPartyResult().get(k);
							if (presc.getParty().getPartyId() == 
										presp.getParty().getPartyId()) {
								presp.setConstituencySeats(
										presp.getConstituencySeats() + 
										presc.getConstituencySeats());
							}
						}
					}
				}
			}
		}
		
		/*
		 * Set it to 0
		 */
		additional_seats_taken = 0;

		/*
		 * At this point we have accumulated constituency seats per party per 
		 * province, and we know how many additional seats each province should 
		 * have and each party should have in total. First thing now is to 
		 * create the Div list from the no of constituency seats 
		 */
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				presp = pr.getPartyResult().get(j);
				presp.createInitDivs();
			}
		}

	}

	//@ post \forall int i; 0 <= i && i < constituency_results.size(); \forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); (isThresholdPassed(constituency_results.get(i).getPartyResult().get(j).getParty())) ==> (constituency_results.get(i).getPartyResult().get(j).getMethod() == ElectionConstants.DANISH_METHOD && constituency_results.get(i).getPartyResult().get(j).getAdditionalSeats() == 0 && constituency_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() == 0 && constituency_results.get(i).getPartyResult().get(j).getDivs().size() == (constituency_results.get(i).getPartyResult().get(j).getConstituencySeats() + 1)); 
	//@ post \forall int i; 0 <= i && i < province_results.size(); \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() == 0; 
	private void prepareStepFive() {
		ProvinceResult pr;
		ConstituencyResult cr;
		PartyResult presp, presc;

		/*
		 * Create inititial divs for all passing parties
		 */
		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			for (int j = 0; j < cr.getPartyResult().size(); j++) {
				presc = cr.getPartyResult().get(j);
				if (isThresholdPassed(presc.getParty())) {
					presc.setMethod(ElectionConstants.DANISH_METHOD);
					presc.createInitDivs();
					presc.setAdditionalSeats(0);
					/*
					 * Additional seats taken on constituency level:
					 * presc.getAdditionalSeatsTaken()
					 * ...is never used
					 */
					presc.setAdditionalSeatsTaken(0);
				}
			}
		}
		
		/*
		 * Set to zero the additional seats taken for
		 * every party in every province
		 */
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				presp = pr.getPartyResult().get(i);
				presp.setAdditionalSeatsTaken(0);
			}
		}
	}

	/**
	 * Method makes sure that the total number of seats in party_result 
	 * list in each constituency result equals the number of constituency
	 * and additional in the party_result list for the same party. Method
	 * also makes sure, that the list of candidates in party_result is
	 * ordered descending by total number of votes
	 */
	//@ post \forall int i; 0 <= i && i < constituency_results.size(); (\forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); (\forall int k; 0 <= k && k < constituency_results.get(i).getPartyResult().size(); (constituency_results.get(i).getPartyResult().get(k).getParty().getPartyId() == constituency_results.get(i).getPartyResult().get(j).getParty().getPartyId()) ==> constituency_results.get(i).getPartyResult().get(j).getTotalSeats() == constituency_results.get(i).getPartyResult().get(k).getConstituencySeats() + constituency_results.get(i).getPartyResult().get(k).getAdditionalSeats()));
	//@ post \forall int i; 0 <= i && i < constituency_results.size(); (\forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); (\forall int k; 1 <= k && k < constituency_results.get(i).getPartyResult().get(j).getCandidateResults().size(); constituency_results.get(i).getPartyResult().get(j).getCandidateResults().get(k).getTotalVotes() <= constituency_results.get(i).getPartyResult().get(j).getCandidateResults().get(k-1).getTotalVotes()));
	private void prepareStepSix() {
		ConstituencyResult cr;
		PartyResult pres;
		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			for (int j = 0; j < cr.getPartyResult().size(); j++) {
				pres = cr.getPartyResult().get(j);
				Collections.sort(pres.getCandidateResults(), new Cmp());
			}
		}
	}

	@SuppressWarnings("unused")
	private int countConstituencySeatsOnNationalLevel() {
		int seats = 0;
		PartyResult pres;
		for (int i = 0; i < national_results.size(); i++) {
			pres = national_results.get(i);
			seats += pres.getConstituencySeats();
		}
		return seats;
	}

	//@ pre seats_total >= 0;
	//@ pre quota > 0;
	//@ pre total_passing_votes > 0;
	//@ pre \forall int j; 0 <= j && j < national_results.size(); national_results.get(j).getAdditionalSeats() == 0;
	//@ pre \exists int j; 0 <= j && j < national_results.size(); national_results.get(j).getConstituencySeats() > 0;
	//@ post seats_total <= ElectionConstants.SEATS_DENMARK;
	//@ post seats_total >= (ElectionConstants.SEATS_DENMARK - national_results.size());
	//@ post \forall int j; 0 <= j && j < national_results.size(); national_results.get(j).isThresholdPassed() ==> national_results.get(j).getTotalSeats() == ((int) ((double) national_results.get(j).getTotalVotes() / quota));
	//@ post \forall int j; 0 <= j && j < national_results.size(); !national_results.get(j).isThresholdPassed() ==> national_results.get(j).getTotalSeats() == 0;
	private void addIntegers() {
		for (int i = 0; i < national_results.size(); i++) {
			if (national_results.get(i).isThresholdPassed()) {
				/* 
				 * 'seats' array is the ratio of parties' votes on national level 
				 * divided with the quota for all passing parties
				 */
				national_results.get(i).setTotalSeats(
						(int) ((double) national_results.get(i).getTotalVotes() / quota));
				seats_total += (int) ((double) national_results.get(i).getTotalVotes() / quota);
			} else {
				/*
				 * Votes are lost here, since party has not passed the threshold
				 */
				national_results.get(i).setTotalSeats(0);
				seats_total += 0;
			}
		}
	}

	//@ pre (ElectionConstants.SEATS_DENMARK - national_results.size()) <= seats_total;
	//@ pre seats_total <= ElectionConstants.SEATS_DENMARK;
	//@ pre seats_total >= (ElectionConstants.SEATS_DENMARK - national_results.size());
	//@ post seats_total >= ElectionConstants.SEATS_DENMARK;
	//@ post seats_total > ElectionConstants.SEATS_DENMARK ==> (\exists int j; 0 <= j && j < national_results.size(); national_results.get(j).isDraw() && (\exists int k; 0 <= k && k < national_results.size(); national_results.get(k).isDraw() && j != k));
	//@ post seats_total == ElectionConstants.SEATS_DENMARK ==> (\forall int j; 0 <= j && j < national_results.size(); !national_results.get(j).isDraw());
	private void breakFractions(/*@ non_null @*/ boolean[] done) {
		int count;
		double highest;
		while(seats_total < ElectionConstants.SEATS_DENMARK) {
			/*
			 * Determine highest fraction (decimal number)
			 */
			highest = -1;
			for (int i = 0; i < national_results.size(); i++) {
				if (national_results.get(i).isThresholdPassed()) {
					if (highest < (double) national_results.get(i).getTotalVotes() / quota - 
							(int)((double) national_results.get(i).getTotalVotes() / quota) 
																			&& done[i] == false) {
						highest = (double) national_results.get(i).getTotalVotes() / quota - 
							(int)((double) national_results.get(i).getTotalVotes() / quota);
					}
				}
			}

			/*
			 * Find the party (or parties) to which it belongs
			 */
			count = 0;
			for (int i = 0; i < national_results.size(); i++) {
				if (national_results.get(i).isThresholdPassed()) {
					if (highest == (double) national_results.get(i).getTotalVotes() / quota - 
							(int)((double) national_results.get(i).getTotalVotes() / quota) 
																			&& done[i] == false) {
						seats_total++; count++;
						national_results.get(i).setTotalSeats(national_results.get(i).getTotalSeats() + 1);
						done[i]=true;
					}
				}
			}

			/*
			 * If several parties have the same remainder AND the total no
			 * of seats exceeds the country total, then the code below 
			 * informs the next step between which parties lots should be
			 * drawn 
			 */
			if (seats_total > ElectionConstants.SEATS_DENMARK) {
				for (int i = 0; i < national_results.size(); i++) {
					if (highest == (double) national_results.get(i).getTotalVotes() / quota - 
							(int)((double) national_results.get(i).getTotalVotes() / quota)) {
						national_results.get(i).setDraw(true);
					}
				}
			}
		}
	}

	//@ pre national_results.size() > 0;
	//@ post (\exists int i; 0 <= i && i < national_results.size(); national_results.get(i).getAdditionalSeats() < 0) ==> \result == true;
	//@ post (\forall int i; 0 <= i && i < national_results.size(); national_results.get(i).getAdditionalSeats() >= 0) ==> \result == false;
	private /*@ pure @*/ boolean checkNoOfNegativeAdditionalSeats() {
		PartyResult pres;
		boolean retval = false;
		for (int i = 0; i < national_results.size(); i++) {
			pres= national_results.get(i);
			if (pres.getAdditionalSeats() < 0) {
				retval = true;
				break;
			}
		}
		return retval;
	}

	/**
	 * Method continues to go through the divisor list, find the highest 
	 * value(s) and then add to divisor list where the highest was found.
	 * It stops when all seats at constituency are taken. If more than 
	 * that were taken method determines between/among which parties lots
	 * should be drawn.   
	 * @param cr ConstituencyResult object which is being modified
	 */
	//@ post cr.getSeatsTaken() >= cr.getConstituency().getConstituencySeats(); 
	//@ post (cr.getSeatsTaken() > cr.getConstituency().getConstituencySeats()) ==> (\exists int j; 0 <= j && j < cr.getPartyResult().size(); cr.getPartyResult().get(j).isDraw() && \exists int k; 0 <= k && k < cr.getPartyResult().size(); cr.getPartyResult().get(j).isDraw() && j != k); 
	//@ assignable constituency_results;
	private /*@ spec_public @*/ void findSeats(
							/*@ non_null @*/ ConstituencyResult cr) {
		/*
		 * Create the inititial divisor list using the d'Hondt method. 
		 * Divisors are 1, 2, 3, etc. Here all party votes are just 
		 * divided with 1, since it is the starting point. More comes 
		 * later to divisor list.
		 */
		cr.createInitDivisorList();

		/*
		 * Within every constituency find the next seat
		 */
		int count = 0; //constituency seats
		double highest;
		Div curr;
		PartyResult pres;
		CandidateResult cres;
	
		/*
		 * The 'best' list is used to save references to certain divs
		 * that might be altered if there is a tie somewhere
		 */
		List<Div> best = new ArrayList<Div>();
		
		/*
		 * As long as there are available seats... 
		 */
		while(cr.getSeatsTaken() < cr.getConstituency().getConstituencySeats()) {
			/*
			 * for-loops which determines the highest value among parties
			 * and independent candidates. There might be more than one.  
			 */
			highest = -1.0;
			for (int j = 0; j < cr.getPartyResult().size(); j++) {
				pres = cr.getPartyResult().get(j);
				curr = pres.getDivs().get(cr.getPartyResult().get(j).getDivs().size()-1); 
				if (curr.getQuotient() >= highest) {
					highest = curr.getQuotient();
				}
			}
			for (int j = 0; j < cr.getIndependentCandidates().size(); j++) {
				cres = cr.getIndependentCandidates().get(j);
				if (!cres.isElected()) {
					if (cres.getTotalVotes() >= highest) {
						highest = cres.getTotalVotes();
					}
				}
			}

			/*
			 * Highest value is now determined. Now find them
			 * and add them to the list
			 */
			count = 0;
			for (int j = 0; j < cr.getPartyResult().size(); j++) {
				pres = cr.getPartyResult().get(j);
				curr = pres.getDivs().get(cr.getPartyResult().get(j).getDivs().size()-1); 
				if (curr.getQuotient() == highest) {
					count++;
					best.add(curr);
					pres.addOneToDivList();
					pres.setConstituencySeats(
							pres.getConstituencySeats() + 1);
					cr.setSeatsTaken(cr.getSeatsTaken()+1);
				}
			}
			for (int j = 0; j < cr.getIndependentCandidates().size(); j++) {
				cres = cr.getIndependentCandidates().get(j);
				if (!cres.isElected()) {
					if (cres.getTotalVotes() == highest) {
						count++;
						best.add(new Div(cres));
						cres.setElected(true);
						cr.setSeatsTaken(cr.getSeatsTaken()+1);
					}
				}
			}
			if (count<=1) {best.clear();}
		}

		/*
		 * If seats taken is higher than seats belonging to 
		 * constituency, then lots must be drawn. Here we 
		 * inform the election officials who they are; they
		 * are either parties or independent candidates
		 */
		if (cr.getSeatsTaken() > cr.getConstituency().getConstituencySeats()) {
			for(int j = 0; j < best.size(); j++) {
				if (best.get(j).getPartyResult() != null) {
					best.get(j).getPartyResult().setDraw(true);
				} else {
					best.get(j).getCandidateResult().setDraw(true);
				}
			}
		}
	}

	/**
	 * Method returns the number of constituency seats taken on national 
	 * levelis and is used by the 'contract' on updateNationalResult
	 * @return Number of constituency seats 
	 */
	@SuppressWarnings("unused") // N.B.: it is used, but only by the "contracts"
	private /*@ pure @*/ int countConstituencySeats() {
		int retval = 0;
		for (int i = 0; i < national_results.size(); i++) {
			retval += national_results.get(i).getConstituencySeats();
		}
		return retval;
	}
	
	/**
	 * Method counts how many parties have passed the threshold. If
	 * non are passing, then no party will get any additional seat
	 * @return Number of passing parties
	 */
	//@ post \exists int i; 0 <= i && i < national_results.size(); national_results.get(i).isThresholdPassed() ==> \result > 0; 
	//@ post \forall int i; 0 <= i && i < national_results.size(); national_results.get(i).isThresholdPassed() ==> \result == national_results.size(); 
	//@ post \forall int i; 0 <= i && i < national_results.size(); !national_results.get(i).isThresholdPassed() ==> \result == 0; 
	private /*@ pure @*/ int countPassingParties() {
		PartyResult pres;
		int retval = 0;
		for (int i = 0; i < national_results.size(); i++) {
			pres = national_results.get(i);
			if (pres.isThresholdPassed()) {
				retval++;
			}
		}
		return retval;
	}

	/*
	 * There is a possibility that two parties in one province
	 * will draw for the last additional seat available for the 
	 * province, or that the same party in two provinces will 
	 * draw for the last additional seat available for the 
	 * party. This method checks if that is the case.
	 */
	//@ post \exists int i; 0 <= i && i < province_results.size(); province_results.get(i).getAdditionalSeatsTaken() > province_results.get(i).getProvince().getAdditionalSeats() ==> \result == true;
	//@ post \exists int i; 0 <= i && i < national_results.size(); national_results.get(i).getAdditionalSeatsTaken() > national_results.get(i).getAdditionalSeats() ==> \result == true;
	//@ post (\forall int i; 0 <= i && i < province_results.size(); province_results.get(i).getAdditionalSeatsTaken() <= province_results.get(i).getProvince().getAdditionalSeats() && \forall int j; 0 <= j && j < national_results.size(); national_results.get(i).getAdditionalSeatsTaken() <= national_results.get(i).getAdditionalSeats()) ==> \result == false;
	private /*@ pure @*/ boolean tooManyAdditionalSeatsTaken() {
		ProvinceResult pr;
		PartyResult presn;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			if (pr.getAdditionalSeatsTaken() > 
					pr.getProvince().getAdditionalSeats()) {
				return true;
			}
		}
		for (int i = 0; i < national_results.size(); i++) {
			presn = national_results.get(i);
			if (presn.getAdditionalSeatsTaken() > presn.getAdditionalSeats()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Locate a PartyResult object in the list 'national_results'
	 * corresponding to party of argument 
	 * @param vp PartyResult object
	 * @return Return a PartyResult object
	 */
	//@ pre national_results.size() > 0;
	//@ post (\exists int i; 0 <= i && i < national_results.size(); pres.getParty().getPartyId() == national_results.get(i).getParty().getPartyId()) ==> \result != null;
	//@ post (\forall int i; 0 <= i && i < national_results.size(); pres.getParty().getPartyId() != national_results.get(i).getParty().getPartyId()) ==> \result == null;
	private PartyResult locatePartyResultOnNationalLevel(/*@ non_null @*/ PartyResult pres) {
		for (int i = 0; i < national_results.size(); i++) {
			if (national_results.get(i).getParty().getPartyId()
					== pres.getParty().getPartyId()) {
				return national_results.get(i);
			}
		}
		return null;
	}

	//@ assignable province_results, additional_seats_taken;
	private void findAdditionalSeats() {
		ProvinceResult pr;
		PartyResult presp;

		double highest, tmp;
		PartyResult presn;
		Div curr;

		/*
		 * Find the highest un-arrested value
		 */
		highest = -1;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			if (pr.getAdditionalSeatsTaken() < pr.getProvince().getAdditionalSeats()) {
				for(int j = 0; j < pr.getPartyResult().size(); j++) {
					presp = pr.getPartyResult().get(j);
					if (isThresholdPassed(presp.getParty())) {
						presn = locatePartyResultOnNationalLevel(presp);
						if (presn.getAdditionalSeatsTaken() < presn.getAdditionalSeats()) {
							tmp = presp.getDivs().get(presp.getDivs().size()-1).getQuotient(); 
							if (highest < tmp) {
								highest = tmp; 
							}
						}
					}
				}
			}
		}
		
		if (highest < 0) {return;}

		/*
		 * Locate the highest value among passing parties
		 */
		int ranking = additional_seats_taken + 1;
		int count = 0;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				presp = pr.getPartyResult().get(j);
				if (isThresholdPassed(presp.getParty())) {
					presn = locatePartyResultOnNationalLevel(presp);
					curr = presp.getDivs().get(presp.getDivs().size()-1);
					if (curr.getQuotient() == highest) {
						count++;

						/*
						 * Set the seat_no on the Div and add it to
						 * the list of winners
						 */
						curr.setRanking(ranking);

						/*
						 * Add 1 to number of additional seats of
						 * a party on provincial level...
						 * ...as well as on the national level
						 */
						presp.addOneToDivList();
						presp.setAdditionalSeats(presp.getAdditionalSeats() + 1);
						presn.setAdditionalSeatsTaken(presn.getAdditionalSeatsTaken()+1);

						/*
						 * ...but also update number of seats 
						 * taken for the province itself 
						 */
						pr.setAdditionalSeatsTaken(pr.getAdditionalSeatsTaken() + 1);
					}
				}
			}
		}

		/*
		 * Accumulate additional seats taken
		 */
		additional_seats_taken += count;
	}

	private List<PartyResult> partiesNotRunningInAllProvinces() {
		List<PartyResult> retval = new ArrayList<PartyResult>();
		ProvinceResult pr;
		PartyResult presn, presp;
		boolean found;
		for (int i = 0; i < national_results.size(); i++) {
			presn = national_results.get(i);
			if (presn.isThresholdPassed() && presn.getAdditionalSeats() > 0) {
				found = false;
				for (int j = 0; j < province_results.size(); j++) {
					pr = province_results.get(j);
					for (int k = 0; k < pr.getPartyResult().size(); k++) {
						presp = pr.getPartyResult().get(k);
						if (presn.getParty().getPartyId() == presp.getParty().getPartyId()) {
							found = true;
						}
					}
				}
				if (!found) {
					retval.add(presn);
				}
			}
		}
		return retval;
	}

	/**
	 * This method creates a boolean array and initializes 
	 * every slot to false  
	 * @return a boolean array
	 */
	// post (\forall int i; 0 <= i && i <= national_results.size(); \result == false);
	private boolean[] initDones() {
		boolean[] retval = new boolean[national_results.size()];
		for (int i = 0; i < retval.length; i++) {
			retval[i] = false;
		}
		return retval;
	}

	//@ post (\forall int j; 0 <= j && j < constituency_results.size(); constituency_results.get(j).getSeatsTaken() == constituency_results.get(j).getConstituency().getConstituencySeats()) ==> \result == true;
	//@ post (\exists int j; 0 <= j && j < constituency_results.size(); constituency_results.get(j).getSeatsTaken() > constituency_results.get(j).getConstituency().getConstituencySeats()) ==> \result == false;
	private /*@ pure @*/ boolean isStep1Resolved() {
		for (int i = 0; i < constituency_results.size(); i++) {
			if (constituency_results.get(i).getSeatsTaken() > 
					constituency_results.get(i).getConstituency().getConstituencySeats()) {
				return false;
			}
		}
		return true;
	}
	
	//@ post (seats_total == ElectionConstants.SEATS_DENMARK) ==> \result == true;
	//@ post (seats_total != ElectionConstants.SEATS_DENMARK) ==> \result == false;
	private /*@ pure @*/ boolean isStep3Resolved() {
		if (seats_total == ElectionConstants.SEATS_DENMARK) {
			return true;
		}
		return false;
	}

	/*
	 * There is a possibility that more than one party in a province
	 * will draw for the last additional seat available. This would
	 * produce a state where too many seats are taken on province 
	 * level. This method checks if that is the case
	 */
	//@ post (\exists int i; 0 <= i && i < province_results.size(); province_results.get(i).getAdditionalSeatsTaken() != province_results.get(i).getProvince().getAdditionalSeats() || \exists int j; 0 <= j && j < national_results.size(); national_results.get(j).getAdditionalSeatsTaken() != national_results.get(j).getAdditionalSeats()) ==> \result == false; 
	//@ post (\forall int i; 0 <= i && i < province_results.size(); province_results.get(i).getAdditionalSeatsTaken() == province_results.get(i).getProvince().getAdditionalSeats() && \forall int j; 0 <= j && j < national_results.size(); national_results.get(j).getAdditionalSeatsTaken() == national_results.get(j).getAdditionalSeats()) ==> \result == true; 
	private /*@ pure @*/ boolean isStep4Resolved() {
		ProvinceResult pr;
		PartyResult presn;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			if (pr.getAdditionalSeatsTaken() != pr.getProvince().getAdditionalSeats()) {
				return false;
			} else {
				for (int j = 0; j < national_results.size(); j++) {
					presn = national_results.get(j);
					if (presn.getAdditionalSeatsTaken() != presn.getAdditionalSeats()) {
						return false;
					}
				}
			}
		}
		return true;
	}

	/**
	 * Method checks if step 5 is resolved or just done
	 * @return Returns true if pruned. False otherwise
	 */
	//@ post (\forall int i; 0 <= i && i < province_results.size(); \forall int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() == province_results.get(i).getPartyResult().get(j).getAdditionalSeats()) ==> \result == true;
	//@ post (\exists int i; 0 <= i && i < province_results.size(); \exists int j; 0 <= j && j < province_results.get(i).getPartyResult().size(); province_results.get(i).getPartyResult().get(j).getAdditionalSeatsTaken() > province_results.get(i).getPartyResult().get(j).getAdditionalSeats()) ==> \result == false;
	private /*@ pure @*/ boolean isStep5Resolved() {
		
		/*
		 * Check if same party in some province has more
		 * additional seats taken than it should
		 */
		ProvinceResult pr;
		PartyResult pres;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				pres = pr.getPartyResult().get(j);
				if (pres.getAdditionalSeatsTaken() > pres.getAdditionalSeats()) {
					return false;
				}
			}
		}
		return true;
	}

	//@ post (\exists int i; 0 <= i && i < constituency_results.size(); \exists int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); !constituency_results.get(i).getPartyResult().get(j).isResolved()) ==> \result == false;
	//@ post (\forall int i; 0 <= i && i < constituency_results.size(); \forall int j; 0 <= j && j < constituency_results.get(i).getPartyResult().size(); constituency_results.get(i).getPartyResult().get(j).isResolved()) ==> \result == true;
	private /*@ pure @*/ boolean isStep6Resolved() {
		ConstituencyResult cr;
		PartyResult pres;
		for (int i = 0; i < constituency_results.size(); i++) {
			cr = constituency_results.get(i);
			for (int j = 0; j < cr.getPartyResult().size(); j++) {
				pres = cr.getPartyResult().get(j);
				if (!pres.isResolved()) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Method determines if the electoral threshold is passed for a certain
	 * party
	 * @param pr PartyResult object which is being investigated
	 * @return Returns true if threshold is passed
	 */
	//@ pre total_valid_votes > 0;
	//@ pre province_results.size() == ElectionConstants.NO_OF_PROVINCES;
	//@ pre national_results.size() > 0;
	//@ post pres.getConstituencySeats() > 0 ==> \result == true;
	//@ post (\exists int i; 0 <= i && i < province_results.size(); \exists int p; 0 <= p && p < province_results.get(i).getPartyResult().size(); (province_results.get(i).getPartyResult().get(p).getParty().getPartyId() == pres.getParty().getPartyId()) && (((double) province_results.get(i).getPartyResult().get(p).getTotalVotes() / (double) province_results.get(i).getProvince().getConstituencySeats()) <= (double) province_results.get(i).getValidVotes()) && (\exists int ii; 0 <= ii && ii < province_results.size(); \exists int pp; 0 <= pp && pp < province_results.get(ii).getPartyResult().size(); (((double) province_results.get(ii).getPartyResult().get(pp).getTotalVotes() / (double) province_results.get(ii).getProvince().getConstituencySeats()) <= (double) province_results.get(ii).getValidVotes()) && (p == pp && i != ii))) ==> \result == true;
	//@ post (( (double) pres.getTotalVotes() / (double) total_valid_votes * 100.0) >= 2.0) ==> \result == true;
	private /*@ pure @*/ boolean isThresholdPassed (PartyResult pres) {
		/*
		 * Threshold A)
		 * Does party have any constituency seat(s)?
		 * A party that has got at least one constituency seat passes
		 * the threshold 
		 */
		if (pres.getConstituencySeats() > 0) {
			return true;
		}

		/*
		 * Threshold B)
		 * Does party have enough votes in 2/3 provinces?
		 * A party that in two out of the three provinces obtains a vote count
		 * that corresponds to at least to:
		 *  total-votes-in-province / constituency-seats-of-province
		 * passes the threshold
		 */
		ProvinceResult pr;
		PartyResult presp;
		int provinces_passed = 0;
		for (int i = 0; i < province_results.size(); i++) {
			pr = province_results.get(i);
			for (int j = 0; j < pr.getPartyResult().size(); j++) {
				presp = pr.getPartyResult().get(j);
				if (presp.getParty().getPartyId() == pres.getParty().getPartyId()) {
					if (((double) pr.getValidVotes() / 
							(double) pr.getProvince().getConstituencySeats())
									<= (double) presp.getTotalVotes()) {
						provinces_passed++;
						if (provinces_passed > 1) {
							return true;
						}
					}
				}
			}
		}

		/*
		 * Threshold C)
		 * Does party have enough votes in country total?
		 * A party that gets at least 2 percent of the votes on national
		 * level passes the threshold
		 */
		if (((double) pres.getTotalVotes() / (double) total_valid_votes * 100) >= 2.0) {
			return true;
		}
		
		// party didn't pass the threshold
		return false;
	}

	/**
	 * Method reads from the list 'national_results' if the threshold
	 * is passed for a certain party. This is determined before hand
	 * @param party Party
	 * @return Returns true if party did pass the threshold
	 */
	private /*@ pure @*/ boolean isThresholdPassed(Party party) {
		PartyResult pres;
		for (int i = 0; i < national_results.size(); i++) {
			pres = national_results.get(i);
			if (pres.getParty().getPartyId() == party.getPartyId()) {
				return pres.isThresholdPassed();
			}
		}
		return false;
	}

	//@ post (\exists int i; 0 <= i && i < national_results.size(); national_results.get(i).isThresholdPassed() && national_results.get(i).getAdditionalSeatsTaken() < national_results.get(i).getAdditionalSeats()) ==> \result == false;  
	//@ post (\forall int i; 0 <= i && i < national_results.size(); national_results.get(i).isThresholdPassed() && national_results.get(i).getAdditionalSeatsTaken() >= national_results.get(i).getAdditionalSeats()) ==> \result == true;  
	private boolean areAllPartiesArrested() {
		PartyResult pres;
		for (int i = 0; i < national_results.size(); i++) {
			pres = national_results.get(i);
			if (pres.isThresholdPassed() && 
					pres.getAdditionalSeatsTaken() < pres.getAdditionalSeats()) {
				return false;
			}
		}
		return true;
	}

}