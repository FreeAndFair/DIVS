package national.process;

import national.data.Ballot;
import national.data.map.PollingStation;
import national.utils.DivsException;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ interface WS_interface {

	/**
	 * Method returns a polling station with a certain ps_id (which
	 * is the id of polling station in the database). First method 
	 * to be called from a polling station is this one.
	 * @param ps_id The id of the polling station in the database
	 * @return Returns a PollingStation object
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	public /*@ pure @*/ PollingStation getPollingStation(int ps_id) throws DivsException;

	/**
	 * Method returns ballot belonging to polling station
	 * @param ps Polling station
	 * @return Returns the ballot balonging to the polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	public /*@ pure @*/ Ballot getBallot(PollingStation ps) throws DivsException;
	
	/**
	 * Get open status of a polling station seen on national level
	 * @param ps Polling station
	 * @return the open status of a certain polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	public /*@ pure @*/ int getOpenStatus(PollingStation ps) throws DivsException;

	/**
	 * Open a polling station received as an argument 
	 * @param ps Polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	public void openPollingStation(PollingStation ps) throws DivsException;

	/**
	 * Closes a certain polling station received as an argument 
	 * @param ps Polling station 
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	public void closePollingStation(PollingStation ps) throws DivsException;

	/**
	 * Method checks if all polling stations have closed
	 * @return Returns true if all have closed. False otherwise
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	public /*@ pure @*/ boolean areAllClosed() throws DivsException;

	/**
	 * Method registeres result coming in from polling station in the 
	 * database (through the database gateway class)
	 * @param ballot Ballot received from polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	public void registerPreliminaryResult(Ballot ballot) throws DivsException;

	/**
	 * Method registeres result coming in from polling station in the 
	 * database (through the database gateway class)
	 * @param ballot Ballot received from polling station
	 * @throws DivsException Throws exception when something is wrong 
	 * 		with e.g. db connection
	 */
	public void registerFinalResult(Ballot ballot) throws DivsException;

}