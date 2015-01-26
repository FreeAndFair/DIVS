package model.process;

import java.util.List;

import model.data.computation.CandidateResult;
import model.data.computation.ConstituencyResult;
import model.data.computation.PartyResult;
import model.data.computation.ProvinceResult;
import model.data.computation.draw.StepFiveDraw;
import model.data.computation.draw.StepFourDraw;
import model.data.computation.draw.StepOneDraw;
import model.data.computation.draw.StepSixDraw;
import model.data.computation.draw.StepThreeDraw;
import model.utils.DivsException;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ interface GUI_interface {

	/**
	 * Initialize the election. Making it ready for handling 
	 * the election.
	 */
	public void initialize();

	/**
	 * Open the election enabling the polling stations to 
	 * open and execute voting at their locations
	 */
	public void openElection();

	/**
	 * Try to close the election. If some polling stations 
	 * are still open then this cannot be done just yet
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	public void tryCloseElection() throws DivsException;

	/**
	 * Check if all preliminary votes are counted and registered 
	 * in the database; i.e. all results are received from the 
	 * polling stations. If all results are received, then it
	 * also loads necessary data from the database and gives
	 * this information to the preliminary result instance
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	public void checkPreliminaryCounting() throws DivsException;

	/**
	 * Step 1 (preliminary):
	 * Method distributes the constituency seats among the 
	 * parties and independent candidate running at the 
	 * different constituencies
	 */
	public void computeStepOnePreliminary();

	/**
	 * Making out the draw after step 1 (preliminary):
	 * After step 1 when there is a draw this method compiles
	 * the involved part into a list. Each element of the
	 * list has the constituency plus the involved parties
	 * and involved independent candidates
	 * @return A list of the draw issues
	 */
	public List<StepOneDraw> getStepOneDrawPreliminary();

	/**
	 * Resolving step 1 (preliminary):
	 * After step 1 there might be parties that are drawing
	 * for the same constituency seat. This method must then
	 * be used to resolve the issue(s).
	 * @param pres The party that is losing the draw
	 * @param cr The constituency where some draw is
	 * @param cres The independent candidate
	 */
	public void resolveStepOnePreliminary(PartyResult pres, 
			CandidateResult cres, ConstituencyResult cr);

	/**
	 * Step 2 (preliminary):
	 * Method determines the electoral threshold for all
	 * parties running in the election. Parties, that don't
	 * pass the threshold will not get a share of the 
	 * additional seats. If no party passes the threshold, 
	 * then no one will get part of the additional seats, and
	 * the computing has finished 
	 */
	public void computeStepTwoPreliminary();

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
	public void computeStepThreePreliminary();

	/**
	 * Making out the draw after step 3 (preliminary):
	 * After step 3 when there is a draw this method compiles
	 * the involved part into an object that contains a list
	 * of all involved parties
	 * @return An object with a list of parties involved
	 */
	public StepThreeDraw getStepThreeDrawPreliminary();

	/**
	 * Resolving step 3 (preliminary):
	 * After step 3 there might be parties that are drawing
	 * for the same seat. This method must then be used to
	 * resolve the issue(s). 
	 * @param pres Party that loses the draw
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	public void resolveStepThreePreliminary(PartyResult pres) throws DivsException;

	/**
	 * Step 4 (preliminary):
	 * Method distributes the additional seats to the
	 * provinces
	 */
	public void computeStepFourPreliminary();

	/**
	 * Step 4 (preliminary):
	 * Method finds all parts involved in a draw after 
	 * allocating additional seats to provincial level
	 * @return A draw object notifying the GUI about the problem
	 */
	public /*@ pure @*/ StepFourDraw getStepFourDrawPreliminary();

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
	public void resolveStepFourPreliminary(int rank, 
			PartyResult p_pres, ProvinceResult p_pr) throws DivsException;

	/**
	 * Step 5 (preliminary):
	 * Method distributes the additional seats to the 
	 * constituencies. Note that no candidates will be elected
	 * in the preliminary step.
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	public void computeStepFivePreliminary() throws DivsException;
	
	/**
	 * Making out the draw after step 5 (preliminary):
	 * After step 5 when there is a draw this method compiles
	 * the involved part into a list. Each element of the
	 * list has the party and the provinces involved plus a
	 * list of all the involved constituencies
	 * @return A list of the draw issues
	 */
	public List<StepFiveDraw> getStepFiveDrawPreliminary();

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
	public void resolveStepFivePreliminary(int ranking, PartyResult pres, ConstituencyResult cr) throws DivsException;

	/**
	 * Check if all final votes are counted and registered in
	 * the database; i.e. all results are received from the 
	 * polling stations. If all results are received, then it
	 * also loads necessary data from the database and gives
	 * this information to the final result instance
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	public void checkFinalCounting() throws DivsException;

	/**
	 * Step 1 (final):
	 * Method distributes the constituency seats among the 
	 * parties and independent candidate running at the 
	 * different constituencies
	 * @throws DivsException Throws exception when something 
	 * 		is wrong with e.g. db connection
	 */
	public void computeStepOneFinal() throws DivsException;

	/**
	 * Making out the draw after step 1 (final):
	 * After step 1 when there is a draw this method compiles
	 * the involved part into a list. Each element of the
	 * list has the constituency plus the involved parties
	 * and involved independent candidates
	 * @return A list of parts involved in a draw
	 */
	public List<StepOneDraw> getStepOneDrawFinal();

	/**
	 * Resolving step 1 (final):
	 * After step 1 there might be parties that are drawing
	 * for the same constituency seat. This method must then
	 * be used to resolve the issue(s).
	 * @param pres The party that is losing the draw
	 * @param cres The independent candidate
	 * @param cr The constituency where some draw is
	 */
	public void resolveStepOneFinal(PartyResult pres, 
				CandidateResult cres, ConstituencyResult cr);

	/**
	 * Step 2 (final):
	 * Method determines the electoral threshold for all
	 * parties running in the election. Parties, that don't
	 * pass the threshold will not get a share of the 
	 * additional seats. If no party passes the threshold, 
	 * then no one will get part of the additional seats, and
	 * the computing has finished 
	 */
	public void computeStepTwoFinal();

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
	public void computeStepThreeFinal();
	
	/**
	 * Making out the draw after step 3 (preliminary):
	 * After step 3 when there is a draw this method compiles
	 * the involved part into an object that contains a list
	 * of all involved parties
	 * @return An object with a list of parties involved
	 */
	public StepThreeDraw getStepThreeDrawFinal();

	/**
	 * Resolving step 3 (final):
	 * After step 3 there might be parties that are drawing
	 * for the same seat. This method must then be used to
	 * resolve the issue(s). 
	 * @param pres Party that loses the draw
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	public void resolveStepThreeFinal(PartyResult pres) throws DivsException;

	/**
	 * Step 4 (final):
	 * Method distributes the additional seats to the
	 * provinces
	 */
	public void computeStepFourFinal();

	/**
	 * Step 4 (final):
	 * Method finds all parts involved in a draw after 
	 * allocating additional seats to provincial level
	 * @return A draw object notifying the GUI about the problem
	 */
	public /*@ pure @*/ StepFourDraw getStepFourDrawFinal();

	/**
	 * Step 4 (final):
	 * Method resolves a draw after allocating additional seats to
	 * provincial level, at least partially. The semantics of the
	 * parameters is that party result in province result wins the
	 * ranking, and therefore all others with the same ranking are
	 * pushed down by 1
	 * @param rank The ranking that ranges from 1 to 40
	 * @param p_pres The party result winning the draw
	 * @param p_pr The province result winning the draw
	 */
	public void resolveStepFourFinal(int rank, 
			PartyResult p_pres, ProvinceResult p_pr) throws DivsException;

	/**
	 * Step 5 (final):
	 * Method distributes the additional seats to the 
	 * constituencies. Note that no candidates will be elected
	 * in the preliminary step.
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	public void computeStepFiveFinal() throws DivsException;
	
	/**
	 * Making out the draw after step 5 (final):
	 * After step 5 when there is a draw this method compiles
	 * the involved part into a list. Each element of the
	 * list has the party and the provinces involved plus a
	 * list of all the involved constituencies
	 * @return A list of the draw issues
	 */
	public List<StepFiveDraw> getStepFiveDrawFinal();

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
	public void resolveStepFiveFinal(int ranking, PartyResult pres, ConstituencyResult cr) throws DivsException;

	/**
	 * Step 6 (final):
	 * Method elects the candidates belonging to parties that
	 * have won seats in the different constituencies. The
	 * method does here not distinguish between constituency
	 * seats and additional seats.
	 * @throws DivsException Throws exception when something 
	 * 				is wrong with e.g. db connection
	 */
	public void computeStepSixFinal() throws DivsException;

	/**
	 * Making out the draw after step 6 (final):
	 * After step 6 when there are draws this method compiles
	 * the involved part into a list. Each element of the
	 * list has the constituenct, the party, and the 
	 * involved candidates
	 * @return A list of the draw issues
	 */
	public List<StepSixDraw> getStepSixDrawFinal();

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
	public void resolveStepSixFinal(ConstituencyResult cr, PartyResult pres, CandidateResult cres) throws DivsException;

	/**
	 * Method returns the result (and is therefore preferable called
	 * after the result is computed)
	 * @return The election's result
	 */
	public /*@ pure @*/ ElectionResult getPreliminaryResult();

	/**
	 * Method returns the result (and is therefore preferable called
	 * after the result is computed)
	 * @return The election's result
	 */
	public /*@ pure @*/ ElectionResult getFinalResult();

}