package model.process;

import java.util.List;

import model.ElectionConstants;
import model.ElectionStatus;
import model.data.Ballot;
import model.data.computation.CandidateResult;
import model.data.computation.ConstituencyResult;
import model.data.computation.PartyResult;
import model.data.computation.ProvinceResult;
import model.data.computation.draw.StepFiveDraw;
import model.data.computation.draw.StepFourDraw;
import model.data.computation.draw.StepOneDraw;
import model.data.computation.draw.StepSixDraw;
import model.data.computation.draw.StepThreeDraw;
import model.data.map.PollingStation;
import model.gateways.database.DatabaseGateway;
import model.utils.DivsException;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Election implements 
							GUI_interface, WS_interface {

	// status of the election
	private int status;
	// gateway to database
	private DatabaseGateway db;
	// instance makes sure it is singleton
	//private Election instance;

	// data used at national level
	private ElectionResult preliminary_result, final_result;

	//@ invariant status == ElectionStatus.BEFORE_ELECTION || status == ElectionStatus.INITIALIZED || status == ElectionStatus.ELECTION_OPEN || status == ElectionStatus.ELECTION_CLOSED || status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED || status == ElectionStatus.PRELIMINARY_RESULTS_COMPUTED || status == ElectionStatus.FINAL_COUNTING_COMPLETED || status == ElectionStatus.FINAL_RESULTS_COMPUTED;
	//@ invariant db != null;

	/**
	 * @param jdbc_driver Database driver
	 * @param db_url Database URL
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	//@ post status == ElectionStatus.BEFORE_ELECTION;
	//@ post db != null;
	//@ post preliminary_result != null;
	//@ post final_result != null;
	//@ assignable status, db, preliminary_result, final_result;
	//@ signals (DivsException d) (d instanceof DivsException);
	public Election(
			/*@ non_null @*/ String jdbc_driver,
			/*@ non_null @*/ String db_url) throws DivsException {
		// initializations
		db = DatabaseGateway.getInstance(jdbc_driver, db_url);
		preliminary_result = new ElectionResult();
		final_result = new ElectionResult();
		status = ElectionStatus.BEFORE_ELECTION;
	}

	/**
	 * GUI should always check this method before calling methods
	 * that have the potential to change states
	 * @return The outer status of the election
	 */
	public /*@ pure @*/ int getStatus() {
		return status;
	}

	/**
	 * @return The database gateway
	 */
	public /*@ pure @*/ DatabaseGateway getDbGw() {
		return db;
	}

	/**
	 * Initialize the election. Making it ready for handling 
	 * the election.
	 * @throws DivsException when something goes wrong
	 */
	//@ pre status == ElectionStatus.BEFORE_ELECTION;
	//@ post status == ElectionStatus.INITIALIZED;
	//@ assignable status;
	public void initialize() {
		status = ElectionStatus.INITIALIZED;
	}

	/**
	 * Open the election enabling the polling stations to 
	 * open and execute voting at their locations
	 */
	//@ pre status == ElectionStatus.INITIALIZED;
	//@ post status == ElectionStatus.ELECTION_OPEN;
	//@ assignable status;
	public void openElection() {
		status = ElectionStatus.ELECTION_OPEN;
	}

	/**
	 * Try to close the election. If some polling stations 
	 * are still open then this cannot be done just yet
	 */
	//@ pre status == ElectionStatus.ELECTION_OPEN;
	//@ post areAllClosed() ==> status == ElectionStatus.ELECTION_CLOSED;
	//@ assignable status;
	//@ signals (DivsException d) (d instanceof DivsException);
	public void tryCloseElection() throws DivsException {
		if (areAllClosed()) {
			status = ElectionStatus.ELECTION_CLOSED;
		}
	}

	/**
	 * Check if all preliminary votes are counted and registered 
	 * in the database; i.e. all results are received from the 
	 * polling stations. If all results are received, then it
	 * also loads necessary data from the database and gives
	 * this information to the preliminary result instance
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.ELECTION_CLOSED;
	//@ post db.checkCounting(ElectionConstants.PRELIMINARY_) ==> (status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED);
	//@ assignable status;
	//@ signals (DivsException d) (d instanceof DivsException);
	public void checkPreliminaryCounting() throws DivsException {
		if (db.checkCounting(ElectionConstants.PRELIMINARY_)) {
			this.prepareFiveSteps(preliminary_result, ElectionConstants.PRELIMINARY_);		
			status = ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
		}
	}

	/**
	 * Step 1 (preliminary):
	 * Method distributes the constituency seats among the 
	 * parties and independent candidate running at the 
	 * different constituencies
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.BEFORE_COMPUTING;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.STEP_1_DONE || preliminary_result.getInnerStatus() == ElectionStatus.STEP_1_RESOLVED;
	//@ assignable preliminary_result;
	//@ signals (DivsException d) (d instanceof DivsException);
	@Override
	public void computeStepOnePreliminary() {
		preliminary_result.allocateConstituencySeats();
	}

	/**
	 * Making out the draw after step 1 (preliminary):
	 * After step 1 when there is a draw this method compiles
	 * the involved part into a list. Each element of the
	 * list has the constituency plus the involved parties
	 * and involved independent candidates
	 * @return A list of the draw issues
	 */
	public /*@ pure @*/ List<StepOneDraw> getStepOneDrawPreliminary() {
		return preliminary_result.getStepOneDraw();
	}

	/**
	 * Resolving step 1 (preliminary):
	 * After step 1 there might be parties that are drawing
	 * for the same constituency seat. This method must then
	 * be used to resolve the issue(s).
	 * @param pres The party that is losing the draw
	 * @param cres The independent candidate
	 * @param cr The constituency where some draw is
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.STEP_1_DONE;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.STEP_1_DONE || preliminary_result.getInnerStatus() == ElectionStatus.STEP_1_RESOLVED;
	//@ assignable preliminary_result;
	@Override
	public void resolveStepOnePreliminary(/*@ non_null @*/ PartyResult pres,
			/*@ non_null @*/ CandidateResult cres, /*@ non_null @*/ ConstituencyResult cr) {
		preliminary_result.resolveConstituencySeats(pres, cres, cr);
	}

	/**
	 * Step 2 (preliminary):
	 * Method determines the electoral threshold for all
	 * parties running in the election. Parties, that don't
	 * pass the threshold will not get a share of the 
	 * additional seats. If no party passes the threshold, 
	 * then no one will get part of the additional seats, and
	 * the computing has finished 
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.STEP_1_RESOLVED;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.THRESHOLD_DETERMINED || preliminary_result.getInnerStatus() == ElectionStatus.NO_PASSING_PARTIES;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.NO_PASSING_PARTIES ==> status == ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
	//@ assignable preliminary_result;
	@Override
	public void computeStepTwoPreliminary() {
		preliminary_result.determineThreshold();
		if (preliminary_result.getInnerStatus() == ElectionStatus.NO_PASSING_PARTIES) {
			status = ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
		}
	}

	/**
	 * Step 3 (preliminary):
	 * Method distributes on national level all the seats
	 * in Denmark. The number of additional seats becomes
	 * the total number minus the number of constituency
	 * seats already taken by the parties. If party has more 
	 * constituency seats than total seats, then party keeps 
	 * its constituency seats, but does not get a share of 
	 * the additional seats.
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.THRESHOLD_DETERMINED;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.STEP_3_DONE || preliminary_result.getInnerStatus() == ElectionStatus.STEP_3_RESOLVED;
	//@ assignable preliminary_result;
	@Override
	public void computeStepThreePreliminary() {
		preliminary_result.allocateAdditionalSeatsToParties();
	}

	/**
	 * Making out the draw after step 3 (preliminary):
	 * After step 3 when there is a draw this method compiles
	 * the involved part into an object that contains a list
	 * of all involved parties
	 * @return An object with a list of parties involved
	 */
	public /*@ pure @*/ StepThreeDraw getStepThreeDrawPreliminary() {
		return preliminary_result.getStepThreeDraw();
	}

	/**
	 * Resolving step 3 (preliminary):
	 * After step 3 there might be parties that are drawing
	 * for the same seat. This method must then be used to
	 * resolve the issue(s). 
	 * @param pres Party that loses the draw
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.STEP_3_DONE;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.STEP_3_DONE || preliminary_result.getInnerStatus() == ElectionStatus.STEP_3_RESOLVED;
	@Override
	public void resolveStepThreePreliminary(/*@ non_null @*/ PartyResult pres) throws DivsException {
		preliminary_result.resolveAdditionalSeats(pres);
	}

	/**
	 * Step 4 (preliminary):
	 * Method distributes the additional seats to the
	 * provinces
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.STEP_3_RESOLVED;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.STEP_4_DONE || preliminary_result.getInnerStatus() == ElectionStatus.STEP_4_RESOLVED;
	//@ assignable preliminary_result;
	@Override
	public void computeStepFourPreliminary() {
		preliminary_result.allocateAdditionalSeatsToProvinces();
	}
	
	/**
	 * Making out the draw after step 5 (preliminary):
	 * After step 5 when there is a draw this method compiles
	 * the involved part into a list. Each element of the
	 * list has the party and the provinces involved plus a
	 * list of all the involved constituencies
	 * @return A list of the draw issues
	 */
	public List<StepFiveDraw> getStepFiveDrawPreliminary() {
		return preliminary_result.getStepFiveDraw();
	}

	/**
	 * Step 4 (preliminary):
	 * Method finds all parts involved in a draw after 
	 * allocating additional seats to provincial level
	 * @return A draw object notifying the GUI about the problem
	 */
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.STEP_4_DONE;
	@Override
	public /*@ pure @*/ StepFourDraw getStepFourDrawPreliminary() {
		return preliminary_result.getStepFourDraw();
	}

	/**
	 * Step 4 (preliminary):
	 * Method resolves a draw after allocating additional seats to
	 * provincial level, at least partially. The semantics of the
	 * parameters is that party result in province result wins the
	 * ranking, and therefore all others with the same ranking are
	 * pushed down by 1
	 * @param rank The ranking that ranges from 1 to 40
	 * @param p_pres The party result winning the draw
	 * @param p_pr The province result winning the draw
	 */
	//@ pre rank > 0;
	@Override
	public void resolveStepFourPreliminary(int rank, 
			/*@ non_null @*/ PartyResult p_pres, 
			/*@ non_null @*/ ProvinceResult p_pr) throws DivsException {
		preliminary_result.resolveStep4draw(rank, p_pres, p_pr);
	}

	/**
	 * Step 5 (preliminary):
	 * Method distributes the additional seats to the 
	 * constituencies. Note that no candidates will be elected
	 * in the preliminary step.
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.STEP_4_RESOLVED;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_DONE || preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED;
	//@ post (preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED) ==> status == ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
	//@ assignable preliminary_result, status;
	@Override
	public void computeStepFivePreliminary() {
		preliminary_result.allocateAdditionalSeatsToConstituencies();
		if (preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED) {
			status = ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
		}
	}

	/**
	 * Resolving step 5 (preliminary):
	 * After step 5 there might be constituencies drawing for
	 * the same seat(s). This method must then be used to 
	 * resolve the issue(s).
	 * @param ranking The ranking (1 or greater)
	 * @param pres The party involved
	 * @param cr The constituency winning the draw
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_COUNTING_COMPLETED;
	//@ pre ranking > 0;
	//@ pre preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_DONE;
	//@ post preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_DONE || preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED;
	//@ post (preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED) ==> status == ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
	//@ assignable preliminary_result, status;
	@Override
	public void resolveStepFivePreliminary(int ranking, 
			/*@ non_null @*/ PartyResult pres, 
			/*@ non_null @*/ ConstituencyResult cr) throws DivsException {
		preliminary_result.resolveConstituencyResult(ranking, pres, cr);
		if (preliminary_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED) {
			status = ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
		}
	}

	/**
	 * Check if all final votes are counted and registered in
	 * the database; i.e. all results are received from the 
	 * polling stations. If all results are received, then it
	 * also loads necessary data from the database and gives
	 * this information to the final result instance
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
	//@ post db.checkCounting(ElectionConstants.FINAL_) ==> (status == ElectionStatus.FINAL_COUNTING_COMPLETED);
	//@ assignable status;
	//@ signals (DivsException d) (d instanceof DivsException);
	public void checkFinalCounting() throws DivsException {
		if (db.checkCounting(ElectionConstants.FINAL_)) {
			this.prepareFiveSteps(final_result, ElectionConstants.PRELIMINARY_);
			this.prepareSixthStep();
			status = ElectionStatus.FINAL_COUNTING_COMPLETED;
		}
	}

	/**
	 * Step 1 (final):
	 * Method distributes the constituency seats among the 
	 * parties and independent candidate running at the 
	 * different constituencies
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.BEFORE_COMPUTING;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_1_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_1_RESOLVED;
	//@ assignable final_result;
	@Override
	public void computeStepOneFinal() {
		final_result.allocateConstituencySeats();
	}

	/**
	 * Making out the draw after step 1 (final):
	 * After step 1 when there is a draw this method compiles
	 * the involved part into a list. Each element of the
	 * list has the constituency plus the involved parties
	 * and involved independent candidates
	 * @return A list of the draw issues
	 */
	public /*@ pure @*/ List<StepOneDraw> getStepOneDrawFinal() {
		return final_result.getStepOneDraw();
	}

	/**
	 * Resolving step 1 (final):
	 * After step 1 there might be parties that are drawing
	 * for the same constituency seat. This method must then
	 * be used to resolve the issue(s).
	 * @param pres The party that is losing the draw
	 * @param cres The independent candidate
	 * @param cr The constituency where some draw is
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_1_DONE;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_1_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_1_RESOLVED;
	//@ assignable final_result;
	@Override
	public void resolveStepOneFinal(/*@ non_null @*/ PartyResult pres, 
			/*@ non_null @*/ CandidateResult cres, /*@ non_null @*/ ConstituencyResult cr) {
		final_result.resolveConstituencySeats(pres, cres, cr);
	}

	/**
	 * Step 2 (final):
	 * Method determines the electoral threshold for all
	 * parties running in the election. Parties, that don't
	 * pass the threshold will not get a share of the 
	 * additional seats. If no party passes the threshold, 
	 * then no one will get part of the additional seats, and
	 * the computing has finished 
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_1_RESOLVED;
	//@ post final_result.getInnerStatus() == ElectionStatus.THRESHOLD_DETERMINED || final_result.getInnerStatus() == ElectionStatus.NO_PASSING_PARTIES;
	//@ post final_result.getInnerStatus() == ElectionStatus.NO_PASSING_PARTIES ==> status == ElectionStatus.FINAL_RESULTS_COMPUTED;
	//@ assignable final_result;
	@Override
	public void computeStepTwoFinal() {
		final_result.determineThreshold();
		if (final_result.getInnerStatus() == ElectionStatus.NO_PASSING_PARTIES) {
			status = ElectionStatus.FINAL_RESULTS_COMPUTED;
		}
	}

	/**
	 * Step 3 (final):
	 * Method distributes on national level all the seats
	 * in Denmark. The number of additional seats becomes
	 * the total number minus the number of constituency
	 * seats already taken by the parties. If party has more 
	 * constituency seats than total seats, then party keeps 
	 * its constituency seats, but does not get a share of 
	 * the additional seats.
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.THRESHOLD_DETERMINED;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_3_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_3_RESOLVED;
	//@ assignable final_result;
	@Override
	public void computeStepThreeFinal() {
		final_result.allocateAdditionalSeatsToParties();
	}

	/**
	 * Making out the draw after step 3 (final):
	 * After step 3 when there is a draw this method compiles
	 * the involved part into an object that contains a list
	 * of all involved parties
	 * @return An object with a list of parties involved
	 */
	public /*@ pure @*/ StepThreeDraw getStepThreeDrawFinal() {
		return final_result.getStepThreeDraw();
	}

	/**
	 * Resolving step 3 (final):
	 * After step 3 there might be parties that are drawing
	 * for the same seat. This method must then be used to
	 * resolve the issue(s). 
	 * @param pres Party that loses the draw
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_3_DONE;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_3_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_3_RESOLVED;
	//@ assignable final_result;
	@Override
	public void resolveStepThreeFinal(/*@ non_null @*/ PartyResult pres) throws DivsException {
		final_result.resolveAdditionalSeats(pres);
	}

	/**
	 * Step 4 (final):
	 * Method distributes the additional seats to the
	 * provinces
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_3_RESOLVED;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_4_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_4_RESOLVED;
	//@ assignable final_result;
	@Override
	public void computeStepFourFinal() {
		final_result.allocateAdditionalSeatsToProvinces();
	}
	
	/**
	 * Step 4 (final):
	 * Method finds all parts involved in a draw after 
	 * allocating additional seats to provincial level
	 * @return A draw object notifying the GUI about the problem
	 */
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_4_DONE;
	//@ post \result != null;
	@Override
	public /*@ pure @*/ StepFourDraw getStepFourDrawFinal() {
		return preliminary_result.getStepFourDraw();
	}

	/**
	 * Step 4 (preliminary):
	 * Method resolves a draw after allocating additional seats to
	 * provincial level, at least partially. The semantics of the
	 * parameters is that party result in province result wins the
	 * ranking, and therefore all others with the same ranking are
	 * pushed down by 1
	 * @param rank The ranking that ranges from 1 to 40
	 * @param p_pres The party result winning the draw
	 * @param p_pr The province result winning the draw
	 */
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_4_DONE;
	//@ pre rank > 0;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_4_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_4_RESOLVED;
	@Override
	public void resolveStepFourFinal(int rank, 
			/*@ non_null @*/ PartyResult p_pres, 
			/*@ non_null @*/ ProvinceResult p_pr) throws DivsException {
		final_result.resolveStep4draw(rank, p_pres, p_pr);
	}

	/**
	 * Step 5 (final):
	 * Method distributes the additional seats to the 
	 * constituencies. Note that no candidates will be elected
	 * in the preliminary step.
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_4_RESOLVED;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_5_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED;
	//@ assignable final_result;
	@Override
	public void computeStepFiveFinal() {
		final_result.allocateAdditionalSeatsToConstituencies();
	}

	/**
	 * Making out the draw after step 5 (final):
	 * After step 5 when there is a draw this method compiles
	 * the involved part into a list. Each element of the
	 * list has the party and the provinces involved plus a
	 * list of all the involved constituencies
	 * @return A list of the draw issues
	 */
	public List<StepFiveDraw> getStepFiveDrawFinal() {
		return final_result.getStepFiveDraw();
	}

	/**
	 * Resolving step 5 (preliminary):
	 * After step 5 there might be constituencies drawing for
	 * the same seat(s). This method must then be used to 
	 * resolve the issue(s).
	 * @param ranking The ranking (1 or greater)
	 * @param pres The party involved
	 * @param cr The constituency winning the draw
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_5_DONE;
	//@ pre ranking > 0;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_5_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED;
	//@ assignable final_result;
	@Override
	public void resolveStepFiveFinal(int ranking, 
			/*@ non_null @*/ PartyResult pres,
			/*@ non_null @*/ ConstituencyResult cr) throws DivsException {
		final_result.resolveConstituencyResult(ranking, pres, cr);
	}

	/**
	 * Step 6 (final):
	 * Method elects the candidates belonging to parties that
	 * have won seats in the different constituencies. The
	 * method does here not distinguish between constituency
	 * seats and additional seats.
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_6_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_6_RESOLVED;
	//@ post (final_result.getInnerStatus() == ElectionStatus.STEP_6_RESOLVED) ==> status == ElectionStatus.FINAL_RESULTS_COMPUTED;
	//@ assignable final_result, status;
	@Override
	public void computeStepSixFinal() {
		final_result.selectCandidates();
		if (final_result.getInnerStatus() == ElectionStatus.STEP_6_RESOLVED) {
			status = ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
		}
	}

	/**
	 * Making out the draw after step 6 (final):
	 * After step 6 when there are draws this method compiles
	 * the involved part into a list. Each element of the
	 * list has the constituenct, the party, and the 
	 * involved candidates
	 * @return A list of the draw issues
	 */
	public List<StepSixDraw> getStepSixDrawFinal() {
		return final_result.getStepSixDraw();
	}

	/**
	 * Resolving step 6 (preliminary):
	 * After step 5 there might for some parties in some 
	 * constituencies be candidates that are drawing; i.e. 
	 * they have got the same number of votes, and at least
	 * one of them should not get elected. This method must
	 * then be used to resolve the issue(s).
	 * @param cr The constituency where the issue is
	 * @param pres The party involved
	 * @param cres A candidate that has lost the draw
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.FINAL_COUNTING_COMPLETED;
	//@ pre final_result.getInnerStatus() == ElectionStatus.STEP_6_DONE;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_6_DONE || final_result.getInnerStatus() == ElectionStatus.STEP_6_RESOLVED;
	//@ post (final_result.getInnerStatus() == ElectionStatus.STEP_6_RESOLVED) ==> status == ElectionStatus.FINAL_RESULTS_COMPUTED;
	//@ assignable final_result, status;
	@Override
	public void resolveStepSixFinal(/*@ non_null @*/ ConstituencyResult cr, 
			/*@ non_null @*/ PartyResult pres, 
			/*@ non_null @*/ CandidateResult cres) throws DivsException {
		final_result.resolveCandidates(cr, pres, cres);		
		if (final_result.getInnerStatus() == ElectionStatus.STEP_6_RESOLVED) {
			status = ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
		}
	}

	/**
	 * Method returns the preliminary result
	 * @return The election's preliminary result
	 */
	@Override
	public /*@ pure @*/ ElectionResult getPreliminaryResult() {
		return preliminary_result;
	}

	/**
	 * Method returns the final result
	 * @return The election's final result
	 */
	@Override
	public /*@ pure @*/ ElectionResult getFinalResult() {
		return final_result;
	}

	/**
	 * Method returns a polling station with a certain ps_id (which
	 * is the id of polling station in the database). First method 
	 * to be called from a polling station is this one.
	 * @param ps_id The id of the polling station in the database
	 * @return Returns a PollingStation object
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	@Override
	public /*@ pure @*/ PollingStation getPollingStation(int ps_id) throws DivsException {
		return db.getPollingStation(ps_id);
	}

	/**
	 * Get open status of a polling station seen on national level
	 * @param ps Polling station
	 * @return the open status of a certain polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	//@ post \result == ElectionStatus.PS_NOT_OPEN || \result == ElectionStatus.PS_OPEN || \result == ElectionStatus.PS_CLOSED;
	@Override
	public /*@ pure @*/ int getOpenStatus(
			/*@ non_null @*/ PollingStation ps) throws DivsException {
		return db.getOpenStatus(ps);
	}
	
	/**
	 * Method returns ballot belonging to polling station
	 * @param ps Polling station
	 * @return Returns the ballot balonging to the polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	//@ pre status == ElectionStatus.ELECTION_OPEN;
	// @ signal (DivsException d) (d instanceof DivsException)
	@Override
	public /*@ pure @*/ Ballot getBallot(
			/*@ non_null @*/ PollingStation ps) throws DivsException {
		return db.getBallot(ps);
	}

	/**
	 * Open a polling station received as an argument 
	 * @param ps Polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	//@ pre status == ElectionStatus.ELECTION_OPEN;
	//@ pre ps.getOpenStatus() == ElectionStatus.PS_NOT_OPEN;
	//@ post db.getPollingStation(ps.getPsId()).getOpenStatus() == ElectionStatus.PS_OPEN;
	@Override
	public void openPollingStation(
			/*@ non_null @*/ PollingStation ps) throws DivsException {
		db.openPollingStation(ps);
	}
	
	/**
	 * Closes a certain polling station received as an argument 
	 * @param ps Polling station 
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	//@ pre status == ElectionStatus.ELECTION_OPEN;
	//@ pre ps.getOpenStatus() == ElectionStatus.PS_OPEN;
	//@ post db.getPollingStation(ps.getPsId()).getOpenStatus() == ElectionStatus.PS_CLOSED;
	@Override
	public void closePollingStation(
			/*@ non_null @*/ PollingStation ps) throws DivsException {
		db.closePollingStation(ps);
	}

	/**
	 * Method checks if all polling stations have closed
	 * @return Returns true if all have closed. False otherwise
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	@Override
	public /*@ pure @*/ boolean areAllClosed() throws DivsException {
		return db.areAllClosed();
	}

	/**
	 * Method registeres result coming in from polling station in the 
	 * database (through the database gateway class)
	 * @param ballot Ballot received from polling station
	 * @throws DivsException Throws exception when something is wrong with e.g. db connection
	 */
	//@ pre status == ElectionStatus.ELECTION_CLOSED;
	@Override
	public void registerPreliminaryResults(/*@ non_null @*/ Ballot ballot) throws DivsException {
		db.registerResult(ballot, ElectionConstants.PRELIMINARY_);		
	}

	/**
	 * Method registeres result coming in from polling station in the 
	 * database (through the database gateway class)
	 * @param ballot Ballot received from polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	//@ pre status == ElectionStatus.PRELIMINARY_RESULTS_COMPUTED;
	@Override
	public void registerFinalResults(Ballot ballot) throws DivsException {
		db.registerResult(ballot, ElectionConstants.FINAL_);
	}

	//@ pre temp_final == ElectionConstants.PRELIMINARY_ || temp_final == ElectionConstants.FINAL_;
	//@ pre res.getInnerStatus() == ElectionStatus.BEFORE_COMPUTING;
	//@ post res.getInnerStatus() == ElectionStatus.STEP_5_RESOLVED;
	//@ signals (DivsException d) (d instanceof DivsException);
	private void prepareFiveSteps(
			/*@ non_null @*/ ElectionResult res, int temp_final) 
													throws DivsException {
		/*
		 * Inform about constituency, national, province result, 
		 * and total no of valid votes casted in the election 
		 */
		res.setConstituencyResult(
				db.getConstituencyResults(temp_final));
		res.setNationalResult(
				db.getNationalResults(temp_final));
		res.setProvinceResult(db.getProvinceResults(temp_final));
		res.setTotalValidVotes(db.countTotalValidVotes(temp_final, 0));
		res.setTotalInvalidVotes(db.countTotalInvalidVotes(temp_final, 0));
	}

	//@ pre final_result != null;
	//@ post final_result.getInnerStatus() == ElectionStatus.STEP_6_RESOLVED;
	//@ signals (DivsException d) (d instanceof DivsException);
	private void prepareSixthStep() throws DivsException {
		/*
		 * Inform about candidate result in the already existing list of 
		 * constituency result
		 */
		db.addCandidatesToConstituencyResults(final_result.getConstituencyResults());
	}

}