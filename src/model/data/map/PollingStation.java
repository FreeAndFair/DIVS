package model.data.map;

import java.io.Serializable;

import model.ElectionStatus;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class PollingStation implements Serializable{

	private static final long serialVersionUID = 1L;

	private int ps_id;
	private String name;
	private District district;
	private int no_of_reg_voters;
	private int open_state;
	
	//@ invariant ps_id > 0;
	//@ invariant name != null;
	//@ invariant district != null;
	//@ invariant no_of_reg_voters >= 0;
	//@ invariant open_state == ElectionStatus.PS_NOT_OPEN || open_state == ElectionStatus.PS_OPEN || open_state == ElectionStatus.PS_CLOSED;  

	/**
	 * @param ps_id ps_id of polling station in the database
	 * @param district District to which polling station belongs
	 * @param name Name of the polling station
	 * @param no_of_voters No of registered voters that belong to polling station
	 */
	//@ pre ps_id > 0;
	//@ pre no_of_voters >= 0;
	public PollingStation (int ps_id, /*@ non_null @*/ District district, 
			/*@ non_null @*/ String name, int no_of_voters) {
		this.ps_id = ps_id;
		this.name = name;
		this.district = district;
		this.no_of_reg_voters = no_of_voters;
		this.open_state = ElectionStatus.PS_NOT_OPEN;
	}
	
	/**
	 * @return The ps_id of the polling station in the database
	 */
	public /*@ pure @*/ int getPsId() {
		return ps_id;
	}

	/**
	 * @return The name of the polling station
	 */
	public /*@ pure @*/ String getName() {
		return name;
	}
	
	/**
	 * @return The no of registered voters that belong to the polling station
	 */
	public /*@ pure @*/ int getNoOfRegVoters() {
		return no_of_reg_voters;
	}

	/**
	 * @return The district to which the polling station belongs
	 */
	public /*@ pure @*/ District getDistrict() {
		return district;
	}

	/**
	 * Method returns the status of this polling station. The open
	 * status of the polling station is either not_open (0), open (1),
	 * or closed (2)
	 * @return The status of the polling station
	 */
	public /*@ pure @*/ int getOpenStatus() {
		return this.open_state;
	}

	/**
	 * Method opens the polling station (seen from national level)
	 */
	//@ assignable open_state;
	//@ pre open_state == ElectionStatus.PS_NOT_OPEN;
	//@ post open_state == ElectionStatus.PS_OPEN;
	public void open() {
		this.open_state = ElectionStatus.PS_OPEN;
	}

	/**
	 * Method closes the polling station (seen from national level)
	 */
	//@ assignable open_state;
	//@ pre open_state == ElectionStatus.PS_OPEN;
	//@ post open_state == ElectionStatus.PS_CLOSED;
	public void close() {
		this.open_state = ElectionStatus.PS_CLOSED;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "PollingStation - name: "+name+";district: "+district.getName()+";no of reg. voters: "+no_of_reg_voters+";open state: "+open_state;
	}

}