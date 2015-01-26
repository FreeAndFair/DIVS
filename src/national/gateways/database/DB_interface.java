package national.gateways.database;

import java.util.List;

import national.data.computation.ConstituencyResult;
import national.data.computation.PartyResult;
import national.data.computation.ProvinceResult;
import national.data.map.PollingStation;
import national.data.Ballot;
import national.utils.DivsException;

/**
 * Interface to the gateway to the database
 * 
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ interface DB_interface {

	/**
	 * Method returns a polling station with a certain ps_id
	 * @param ps_id Id of polling station in the database
	 * @return Polling station
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ PollingStation getPollingStation(int ps_id) throws DivsException;

	/**
	 * Method returns the ballot belonging to a certain polling
	 * station. Ballot contains a socalled journal with everything 
	 * that the voter can cast his/her vote on
	 * @param ps Polling station to which the ballot belongs
	 * @return Ballot belonging to a certain district
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ Ballot getBallot(PollingStation ps) throws DivsException;
	
	/**
	 * Method registeres the preliminary or final result of a polling 
	 * station in the database
	 * @param ballot Ballot belonging to a polling station
	 * @param temp_final Either preliminary or final result
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public void registerResult(Ballot ballot, int temp_final) throws DivsException;

	/**
	 * Method fetches all counted votes from the database grouped by 
	 * party and constituency. Constituency results also contain 
	 * the independent candidates
	 * @return List of results from constituency  
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ List<ConstituencyResult> getConstituencyResult(int temp_final) throws DivsException;

	/**
	 * Method add to the list of results from constituency the party
	 * result, which consists among other things of the candidates
	 * running for the party. Method must therefore be callled before 
	 * computing step 6. 
	 * @param List of constituency results already existing  
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public void addCandidatesToConstituencyResult(
			List<ConstituencyResult> const_result) throws DivsException;

	/**
	 * Method fetches all counted votes from the database grouped by
	 * party on national level.
	 * @return Returns a list of party result
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ List<PartyResult> getNationalResult(
									int temp_final) throws DivsException;

	/**
	 * Method fetches all counted votes from the database grouped by
	 * party and province. 
	 * @return Returns a list of province result 
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ List<ProvinceResult> getProvinceResult(
										int temp_final) throws DivsException;

	/**
	 * Method calculates the total number of valid votes casted in 
	 * the election
	 * @param temp_final Either preliminary or final result
	 * @param pid Province id in the database
	 * @return Returns the total number of valid votes
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ int countTotalValidVotes(
				int temp_final, int pid) throws DivsException; 

	/**
	 * Method calculates the total number of INvalid votes casted in
	 * the election
	 * @param temp_final Either preliminary or final result
	 * @param pid Province id in the database. If 0 then all are in
	 * @return Returns the total number of INvalid votes
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ int countTotalInvalidVotes(
				int temp_final, int pid) throws DivsException;

	/**
	 * Method opens a certain polling station and saves the state in
	 * the database
	 * @param ps The polling station
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public void openPollingStation(PollingStation ps) throws DivsException;

	/**
	 * Method closes a certain polling station and saves the state
	 * in the database
	 * @param ps The polling station
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public void closePollingStation(PollingStation ps) throws DivsException;

	/**
	 * Method reads the open state of a polling station from the 
	 * database
	 * @param ps The polling station
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ int getOpenStatus(PollingStation ps) throws DivsException;

	/**
	 * Method checks if all polling stations have closed
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ boolean areAllClosed() throws DivsException;

	/**
	 * Method checks if all polling stations have submitted their 
	 * preliminary or final result
	 * @param temp_final Preliminary or final counting 
	 * @return Returns true if all results are submited. False otherwise
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ boolean checkCounting(int temp_final) throws DivsException;

}