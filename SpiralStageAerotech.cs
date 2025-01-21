//版本号：2.0.9
//综合版本
//修改内容：
////修改移动停止等待逻辑，添加防呆参数检测
////运行脚本增加实时错误查询用于脚本运行中轴异常终止脚本未报错的情况
//增加内容：
////增加停止逻辑
////PIN初始化避让逻辑
////开放同心圆圈数设置
////增加初始化时对于轴状态判断用于执行是否Reset
///增加设置t轴触发起始角度的接口---20240929
///增加T轴初始运行触发角度设定接口---20241014
///增加对外判断吸附压力接口---20241014
///修改Stage下发升降方式给固定值的Bug---20241022
///Stage Abort接口增加等待完成逻辑---20241023
///修改预聚焦距离边缘的测试起点---20241029
///修改Z轴预聚焦高度被扫描前覆盖的Bug---20241029
///增加用于补偿Z轴预聚焦高度的参数接口和设定---20241030
///增加用于上位机独立控制的开关门和吸附释放以及对应的底层IO读写分配控制器独立的任务ID4---20241030
///增加用于上位机控制的升降PIN升降Chuck---20241031
///增加配置文件用于中英文切换配置---20241108
///修改初始化无片升PIN不降的问题---20241121
///初始化在无片时关闭吸附用于碳化硅Chuck,有片时在支撑位则通过吸附有无来判断Wafer是否在Chuck上，在则移开支撑PIN，不在则开吸附---20241125
///增加针对68兼容PIN的位置要改变的逻辑，硬件加了IO用于检测Wafer在8寸的位置，用于校核Wafer尺寸下发与带片时的Wafer尺寸不一致的问题---20241211，未测试
///增加接收上位机发送的大颗粒位置时间信息用于启动IO控制通知PLC控制激光避让PLC---2024/12/18，未测试,12/20测试
///增加AF相关数据采集流程---2024/12/19,未测试，暂时不启用
///临时屏蔽开关门用于验证是否还需要此门---2024/12/23
///添加用于保存APPData相关控制参数和逻辑---2024/12/25待测试
///添加用于保存APPData的频率次数参数，用于自动根据扫描频率进行保存---2024/12/27待测试
///修改PIN尺寸避让逻辑，在下发参数时进行PIN的控制---2024/12/27待测试
//定型时间：202411223

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.Windows.Forms;
using Aerotech.Automation1.DotNet;
using System.IO;
using System.Threading;
using System.Reflection;
using Newtonsoft.Json.Linq;
using static System.Net.Mime.MediaTypeNames;
using System.Net.NetworkInformation;
using System.Runtime.InteropServices;
using System.Drawing.Design;

namespace AK.HW.Stage
{
    public class SpiralStageAerotech
    {
        private Controller _controller = null;
        private ConfiguredParameters _controllerParameters = new ConfiguredParameters();
        private Dictionary<StageOutPutIO, int> _outPutIOs = new Dictionary<StageOutPutIO, int>();
        private Dictionary<StageInputIO, int> _inPutIOs = new Dictionary<StageInputIO, int>();
        private StageRunPara _stageRunPara = new StageRunPara();
        private StageIOPara _stageIOPara = new StageIOPara();
        private List<double> _triggleAngles = new List<double>();
        private List<double> _triggleFres = new List<double>();
        private StatusItemConfiguration _statusItemConfiguration = new StatusItemConfiguration();
        private bool _paraChangeFlag = false;
        private bool _runFlag = false;
        private bool _OpenFlag = true;
        /// <summary>
        /// 保存当前出错信息ID
        /// </summary>
        private int _errorID = 0;
        /// <summary>
        /// 用于计算基准焦距下针对不同厚度晶圆的
        /// </summary>
        private double _AFZOffset = 0;
        public bool IsOpened { get; set; } = false;
        private bool _bStopScan = false;
        private string mLastError = "";
        private bool _initialFlag = false;
        //常量参数后续可能需要写进配置文件
        double[] _Fovs = new double[3] { 4.0, 4.0, 2.0 }; //6 8 12
        double[] _ScanRadius = new double[3] { 80.0, 104.0, 154.0 };
        List<Tuple<int, double>> _BinFreqsFor8 = new List<Tuple<int, double>>();
        private static readonly object _mux = new object();
        private WaferUpDownMode _WaferUpDownMode = WaferUpDownMode.Undefined;
        private LanguageMode _languageMode = LanguageMode.CH;
        private int _StageTaskId = 3;//用于Stage扫描时上位机调用所用的Task  扫描用的Task是1，AF是 2 ，默认的接口用的是1
        private static readonly object _IOLock = new object();//用于Stage的IO接口
        private static readonly object _GIOLock = new object();
        DataCollectionResults _RealStageData;
        private int _ScanCount = 1;
        enum FwaferSize
        {
            FwaferSize6 = 6,
            Fwafersize8 = 8,
            Fwafersize12 = 12,
        }
        enum FScanGrade
        {
            FScanHSpeed = 2,
            FScanStandard = 0,
            FScanHPrecision = 1
        }
        
        public SpiralStageAerotech()
        {
            _BinFreqsFor8.Add(Tuple.Create(8, 20833.3333));
            _BinFreqsFor8.Add(Tuple.Create(4, 41666.6666));
            _BinFreqsFor8.Add(Tuple.Create(8, 65000.0));
            try
            {
                int languageMode = ReadLanguage();
                if (languageMode == (int)LanguageMode.CH)
                {
                    _languageMode = LanguageMode.CH;
                }
                else
                {
                    _languageMode = LanguageMode.EN;
                }
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        const int WaitTime = 5000;
        const int Count = 24;
        public bool Connect()
        {
            try
            {
                //if (Monitor.TryEnter(_mux, 10000))
                //{
                if (_controller != null)
                {
                    _controller.Disconnect();
                    _controller = null;
                }
                //_controller = Controller.Connect("192.168.253.10");
                //_controller = Controller.Connect(_stageRunPara._IP);
                string StageError = null;
                for (int i = 0; i < Count; ++i)
                {
                    try { _controller = Controller.Connect("192.168.253.10"); }
                    catch (Exception ex)
                    {
                        RecordLog(ex.Message);
                        StageError = ex.Message;
                    }
                    if (_controller != null)
                    {
                        break;
                    }
                    Thread.Sleep(WaitTime);
                }
                if (_controller == null)
                {
                    if (_languageMode == LanguageMode.EN)
                    {
                        string error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ConnectStageFault] + StageError;
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    else
                    {
                        string error = StageErrorInfoZ.连接Stage故障.ToString() + StageError;
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
                Start();
                ConfigAxisStatus();
                //UpdateStageRunPara();
                return true;
                // }
                // else 
                // { 
                //     throw new Exception("WaitStageConnectTimeOut");
                // }

            }
            catch (Exception ex)
            {
                string sErrorMessage = $"连接Stage失败!\r\n{ex.Message}\r\n{ex.StackTrace}";
                RecordLog(sErrorMessage);
                Trace.WriteLine(sErrorMessage);
                throw ex;
            }
            // finally { Monitor.Exit(_mux); }

        }
        public void Disconnect()
        {
            try
            {
                //if (Monitor.TryEnter(_mux, 10000))
                {
                    if (_controller != null)
                    {
                        Stop();
                        _controller.Disconnect();
                    }
                }
                //   else { throw new Exception("WaitStageDisConnectTimeOut"); }
            }
            catch (Exception ex)
            {
                RecordLog(ex.Message);
                string sErrorMessage = $"连接Stage失败!\r\n{ex.Message}\r\n{ex.StackTrace}";
                // MessageBox.Show(sErrorMessage);
                Trace.WriteLine(sErrorMessage);
                throw ex;
            }
            //finally { Monitor.Exit(_mux); }

        }
        public bool STAGE_INITIALIZE(bool bForceHome = true)
        {
            // 连接Stage
            string error;
            if (!Connect())
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ConnectStageFault]);
                else
                    throw new Exception(StageErrorInfoZ.连接Stage故障.ToString());
            }

            //后期由上层传递参数实现
            UpdateStageIOPara();
            if (!_loadParaFlag)
            {
                if (_languageMode == LanguageMode.EN)
                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.SystemParaNotSet];
                else
                    error = StageErrorInfoZ.系统参数未设置.ToString();
                RecordLog(error);
                throw new Exception(error);
            }
            ClearException();
            ResetState();
            Thread.Sleep(1000);
            Abort();
            //有料需要吸附再回零
            if (!isAxisNormal())
            {
                Reset();
            }

            if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPinWithSize)
            {
                CheckIfChangePinSizePos(false);
            }
            if (IsWaferExist())
            {
                //throw new Exception("初始化失败：请先人工取出Chunk上的晶圆！");
                //SetIO("Z", _stageIOPara._Fix, true);
                SetIO("Z", _stageIOPara._Fix, false);
                switch (_WaferUpDownMode)
                {
                    case WaferUpDownMode.UpDownPinInChhuck:
                    case WaferUpDownMode.UpDownPinOutChuck:
                        {
                            //判断PIN是否升起，升起需要降落，防止干涉
                            if (IsPinUp())
                            {
                                DownPin();
                            }

                            if (!Fix())
                            {
                                if (_languageMode == LanguageMode.EN)
                                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault];
                                else
                                    error = StageErrorInfoZ.晶圆吸附故障.ToString();
                                RecordLog(error);
                                throw new Exception(error);
                            }
                        }
                        break;
                    case WaferUpDownMode.UpDownChuckFixPin:
                        {
                            if (isPinInAvoidPos())
                            {
                                if (!Fix())
                                {
                                    if (_languageMode == LanguageMode.EN)
                                        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault];
                                    else
                                        error = StageErrorInfoZ.晶圆吸附故障.ToString();
                                    RecordLog(error);
                                    throw new Exception(error);
                                }
                            }
                            else
                            {
                                if (FixNotTimeOut()) //片子在Wafer上，移开支撑PIN到避让位置
                                {
                                    ChangePinPosWithInitAvoidance(true);
                                }
                                else
                                {
                                    SetIO("Z", _stageIOPara._Fix, false);
                                }
                                #region 非碳化硅Chuck需要考虑的逻辑一点点移动直到Wafer与Chuck脱离
                                //if (!Release())
                                //{
                                //    {
                                //        if (_languageMode == LanguageMode.EN)
                                //            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ReleaseWaferFault];
                                //        else
                                //            error = StageErrorInfoZ.晶圆释放故障.ToString();
                                //        RecordLog(error);
                                //        throw new Exception(error);
                                //    }
                                //}
                                //double rpos = -3;//如果正好在停靠位与Wafer脱离
                                //double zv = 3;
                                //try
                                //{
                                //    MoveAxisRelative("Z", rpos, zv);
                                //}
                                //catch (Exception e)
                                //{
                                //    StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);

                                //    AxisFault z = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "Z"].Value;
                                //    if (z == AxisFault.CcwEndOfTravelLimitFault
                                //        || z == AxisFault.CwEndOfTravelLimitFault
                                //        || z == AxisFault.CcwSoftwareLimitFault
                                //        || z == AxisFault.CwSoftwareLimitFault)
                                //    {
                                //        RecordLog(e.Message);
                                //    }
                                //    else { RecordLog(e.Message); throw e; }
                                //}
                                //SetIO("Z", _stageIOPara._Fix, false);
                                #endregion
                            }
                        }
                        break;
                    case WaferUpDownMode.UpDownChuckFixPinNoAvoid:
                        {
                            if (_languageMode == LanguageMode.EN)
                                throw new Exception("初始化失败：请先人工取出Chunk上的晶圆！");
                            else
                                throw new Exception("Initialize Failed: Please Unload Wafer from Chunk Manually");
                        }
                        break;
                    case WaferUpDownMode.UpDownFixPinAndChuck:
                    case WaferUpDownMode.UpDownChuckFixPinWithSize:
                        {
                            if (!Fix())
                            {
                                if (_languageMode == LanguageMode.EN)
                                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault];
                                else
                                    error = StageErrorInfoZ.晶圆吸附故障.ToString();
                                RecordLog(error);
                                throw new Exception(error);
                            }
                        }
                        break;
                    default:
                        {
                            if (_languageMode == LanguageMode.EN)
                                error = "The lifting method for the wafer has not been configured";
                            else
                                error = "升降Wafer的方式未配置";
                            RecordLog(error);
                            throw new Exception(error);
                        }
                        break;
                }




            }
            else
            {
                SetIO("Z", _stageIOPara._Fix, true);//针对碳化硅chuck不能一直无片吸真空会导致真空压力值不够
                switch (_WaferUpDownMode)
                {
                    case WaferUpDownMode.UpDownPinInChhuck:
                    case WaferUpDownMode.UpDownPinOutChuck:
                        {
                            //判断PIN是否升起，升起需要降落，防止干涉
                            if (IsPinUp())
                            {
                                DownPin();
                            }
                        }
                        break;
                }
            }
            //SetIO("Z", _stageIOPara._Fix, true);
            //SetIO("Z", _stageIOPara._Fix, false);
            EnableAll();
            _runFlag = false;
            //互锁逻辑
            try
            {
                if (!IsEFEMInterLockOutEnable())
                {
                    // if (IsOnLoadPos())
                    //     SetEFEMInterLockIn(true);
                    if(_languageMode == LanguageMode.EN)
                        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock];
                    else
                        error = StageErrorInfoZ.触发EFEM互锁.ToString();
                    RecordLog(error);
                    throw new Exception(error);
                }
                if (!IsAirPressureReady())
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.AirFault]);
                    else
                        throw new Exception(StageErrorInfoZ.正压故障.ToString());
                }
                SetEFEMInterLockIn(false);
                /* //AxesSelectionCommands Axes = myController.Commands.Axes;
                 _controller.Commands.Axes["X"].Motion.Setup.RampRate(new double[] { paramBFAOI.MoveAccelration });
                 _controller.Commands.Axes["Y"].Motion.Setup.RampRate(new double[] { paramBFAOI.ScanAccelration });
                 _controller.Commands.Axes["Z"].Motion.Setup.RampRate(new double[] { paramBFAOI.FocusAccelration });*/
                //加载系统参数
                SetStageRunParaGlobal();
                ResetState();
                //SetStageRunParaGlobal();
                if (!Home())
                {
                    Disconnect();
                    return false;
                }
                IsOpened = true;
                _initialFlag = true;
                return true;
            }
            catch (Exception ex)
            {
                RecordLog(ex.Message);
                throw ex;
            }
        }
        public void STAGE_STOP()
        {
            _bStopScan = true;
            Abort();
        }
        /// <summary>
        /// Y对应旋转轴T
        /// </summary>
        /// <param name="bLocateX"></param>
        /// <param name="bLocateT"></param>
        /// <param name="bLocateZ"></param>
        /// <returns></returns>
        public double[] LocateXYZ(bool bLocateX = true, bool bLocateT = true, bool bLocateZ = true)
        {
            double[] aXYZPosition = new double[4] { 0, 0, 0, 0 };
            if (!IsOpened)
                return aXYZPosition;
            if (_controller == null)
                return aXYZPosition;
            if (!_controller.IsRunning)
                return aXYZPosition;
            try
            {
                StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);
                //ControllerDiagPacket cPacket = _controller.DataCollection.RetrieveDiagnostics();
                //原始反馈位置
                //aXYZPosition[0] = cPacket["X"].PositionFeedback;
                //aXYZPosition[1] = cPacket["Y"].PositionFeedback;
                //aXYZPosition[2] = cPacket["Z"].PositionFeedback;
                //修正后位置
                aXYZPosition[0] = result.Axis[AxisStatusItem.PositionFeedback, "X"].Value;
                aXYZPosition[1] = result.Axis[AxisStatusItem.PositionFeedback, "Z"].Value;//cPacket["Y"].ProgramPositionFeedback;
                aXYZPosition[2] = result.Axis[AxisStatusItem.PositionFeedback, "Theta"].Value;//cPacket["Z"].ProgramPositionFeedback;
                                                                                              //double fxx = cPacket["X"].PositionFeedbackAuxiliary;
                                                                                              //double fyy = cPacket["Y"].PositionFeedbackAuxiliary;
                                                                                              //double fzz = cPacket["Z"].PositionFeedbackAuxiliary;
                                                                                              // aXYZPosition[3] = cPacket[AxisMask.A2].AnalogInput0;
            }
            catch (Exception ex)
            {
                Debug.WriteLine("$$##%% - 位置反馈异常");
                mLastError = ex.Message;
                RecordLog(ex.Message);
                throw new Exception(ex.Message);
            }
            return aXYZPosition;
        }

        public bool STAGE_MOVE(double fx = double.NaN, double ft = double.NaN, double fz = double.NaN)
        {
            return MoveToXZT(fx, ft, fz);
        }
        public bool STAGE_MOTION_DONE()
        {
            if (!IsOpened)
                return false;
            return true;
        }

        public bool STAGE_MOVE_RELATIVE(double fdx = double.NaN, double fdy = double.NaN, double fdz = double.NaN)
        {
            return true;
        }
        public void SET_PARAM(string sAxis = "", double fVelocity = double.NaN, double fAccelration = double.NaN)
        {

        }
        public bool STAGE_MOVEDZ(double dz, double speed)
        {
            if (double.IsNaN(dz))
                return false;
            if (Math.Abs(dz) > 1)
                return false;
            try
            {
                //_controller.Commands.Axes["Z"].Motion.MoveInc(new double[] { dz }, new double[] { speed });
                //_controller.Commands.Axes["Z"].Motion.WaitForMotionDone(Aerotech.Ensemble.Commands.WaitOption.MoveDone);//-WCZ
                //myController.Commands.Axes["Z"].Motion.WaitForMotionDone(Aerotech.Ensemble.Commands.WaitOption.InPosition);//-WCZ
                //double[] aPosition = StageAerotech.Instance.STAGE_LOCATION();
                //Debug.WriteLine("$$##%% - Z轴聚焦后位置为{0}", aPosition[2]);
                MoveAxisInc("Z", dz, speed);
            }
            catch (Exception ex)
            {
                Debug.WriteLine("$$$###%%%===  - 相对聚焦异常");
                homeAxis("Z");
                //  double ZPosition = -1.30;
                // MoveToXZT(double.NaN, double.NaN, ZPosition);
                return false;
            }
            return true;
        }
        public bool MoveToZ(double fz, double Speed)
        {
            if (double.IsNaN(fz))
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception("Z Set Positon is NaN");
                else
                    throw new Exception("Z 设定位置是无效的");
            }
            try
            {
                //_controller.Commands.Axes["Z"].Motion.MoveAbs(new double[] { fz }, new double[] { Speed });
                // _controller.Commands.Axes["Z"].Motion.WaitForMotionDone(Aerotech.Ensemble.Commands.WaitOption.MoveDone);//-WCZ
                //myController.Commands.Axes["Z"].Motion.WaitForMotionDone(Aerotech.Ensemble.Commands.WaitOption.InPosition);//-WCZ
                MoveAxis("Z", fz, Speed);
            }
            catch (Exception ex)
            {
                RecordLog(ex.Message);
                throw new Exception(ex.Message);
                mLastError = ex.Message;
                return false;
            }
            return true;
        }
        /// <summary>
        /// 用于主动获取状态
        /// </summary>
        private void ConfigAxisStatus()
        {
            _statusItemConfiguration.Axis.Add(AxisStatusItem.DriveStatus, "X");
            _statusItemConfiguration.Axis.Add(AxisStatusItem.DriveStatus, "Z");
            _statusItemConfiguration.Axis.Add(AxisStatusItem.DriveStatus, "Theta");

            _statusItemConfiguration.Axis.Add(AxisStatusItem.AxisStatus, "X");
            _statusItemConfiguration.Axis.Add(AxisStatusItem.AxisStatus, "Z");
            _statusItemConfiguration.Axis.Add(AxisStatusItem.AxisStatus, "Theta");

            _statusItemConfiguration.Axis.Add(AxisStatusItem.PositionFeedback, "X");
            _statusItemConfiguration.Axis.Add(AxisStatusItem.PositionFeedback, "Z");
            _statusItemConfiguration.Axis.Add(AxisStatusItem.PositionFeedback, "Theta");

            _statusItemConfiguration.Axis.Add(AxisStatusItem.AxisFault, "X");
            _statusItemConfiguration.Axis.Add(AxisStatusItem.AxisFault, "Z");
            _statusItemConfiguration.Axis.Add(AxisStatusItem.AxisFault, "Theta");
        }
        /// <summary>
        /// 升PIN之前必须要把旋转轴转至固定角度（只有在该角度下PIN才能升起来）
        /// 升PIN时Z轴的位置需要移到上下料时Z轴的位置，即取放片示教点位Z轴位置，保证升PIN不会与镜头干涉
        /// 升PIN时要保证先释放晶圆
        /// </summary>
        /// <returns></returns>
        //public bool UpPin()
        //{
        //    if (IsPinUp())
        //        return true;
        //    string error;
        //    MoveAxis("Theta", _stageRunPara._TLoadPos, 100);
        //    MoveAxis("Z", _stageRunPara._ZLoadPos, 20);
        //    if (IsWaferExist())
        //    {
        //        if (!Release())
        //        {
        //            error = StageErrorInfoE.ReleaseWaferFault.ToString();
        //            RecordLog(error);
        //            throw new Exception(error);
        //        }
        //    }
        //    SetIO("Z", _stageIOPara._PinControl, true);
        //    Thread.Sleep(10);
        //    int counter = 0;
        //    while (GetIO("Z", _stageIOPara._PinDown) || !GetIO("Z", _stageIOPara._PinUp))
        //    {
        //        Thread.Sleep(10);
        //        SetIO("Z", _stageIOPara._PinControl, true);
        //        counter++;
        //        if (counter > MAXNUM)
        //        {
        //            error = StageErrorInfoE.WaferPinUpDownFault.ToString();
        //            RecordLog(error);
        //            throw new Exception(error);
        //        }// return false;
        //    }
        //    if (!GetIO("Z", _stageIOPara._PinDown) && GetIO("Z", _stageIOPara._PinUp))
        //        return true;
        //    else
        //    {
        //        error = StageErrorInfoE.WaferPinUpDownFault.ToString();
        //        RecordLog(error);
        //        throw new Exception(error);
        //    }//return false;
        //}
        public bool UpPin()
        {
            if (IsPinUp())
                return true;
            string error;
            if (_WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
            {
                MoveAxis("Theta", _stageRunPara._TLoadPos, 100);
                MoveAxis("Z", _stageRunPara._ZLoadPos, 20);
                if (IsWaferExist())
                {
                    if (!Release())
                    {
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoE.ReleaseWaferFault.ToString();
                        else
                            error = StageErrorInfoZ.晶圆释放故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
                SetIO("Z", _stageIOPara._PinControl, false);
                SetIO("Z", _stageIOPara._PinControlDown, false);
                Thread.Sleep(100);
                SetIO("Z", _stageIOPara._PinControl, true);
                Thread.Sleep(10);
                int counter = 0;
                while (GetIO("Z", _stageIOPara._PinDown) || !GetIO("Z", _stageIOPara._PinUp))
                {
                    Thread.Sleep(10);
                    SetIO("Z", _stageIOPara._PinControl, true);
                    counter++;
                    if (counter > MAXNUM)
                    {
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoE.WaferPinUpDownFault.ToString();
                        else
                            error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }// return false;
                }
                if (!GetIO("Z", _stageIOPara._PinDown) && GetIO("Z", _stageIOPara._PinUp))
                    return true;
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoE.WaferPinUpDownFault.ToString();
                    else
                        error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                    RecordLog(error);
                    throw new Exception(error);
                }//return false;
            }
            else if(_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck) 
            {
                MoveAxis("Theta", _stageRunPara._TLoadPos, 100);
                MoveAxis("Z", _stageRunPara._ZLoadPos, 20);
                if (IsWaferExist())
                {
                    if (!Release())
                    {
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoE.ReleaseWaferFault.ToString();
                        else
                            error = StageErrorInfoZ.晶圆释放故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
                SetIO("Z", _stageIOPara._PinControl, true);
                Thread.Sleep(10);
                int counter = 0;
                while (GetIO("Z", _stageIOPara._PinDown) || !GetIO("Z", _stageIOPara._PinUp))
                {
                    Thread.Sleep(10);
                    SetIO("Z", _stageIOPara._PinControl, true);
                    counter++;
                    if (counter > MAXNUM)
                    {
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoE.WaferPinUpDownFault.ToString();
                        else
                            error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }// return false;
                }
                if (!GetIO("Z", _stageIOPara._PinDown) && GetIO("Z", _stageIOPara._PinUp))
                    return true;
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoE.WaferPinUpDownFault.ToString();
                    else
                        error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                    RecordLog(error);
                    throw new Exception(error);
                }//return false;
            }
            else 
            {
                if (_languageMode == LanguageMode.EN)
                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                else
                    error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                RecordLog(error);
                throw new Exception(error);
            }
        }

        /// <summary>
        /// 不能单独使用，必须在MoveToLoadPos内部使用
        /// </summary>
        /// <returns></returns>
        /// <exception cref="Exception"></exception>
        //private bool UpPinFast()
        //{
        //    if (IsPinUp())
        //        return true;
        //    string error;
        //    SetIO("Z", _stageIOPara._PinControl, true);
        //    Thread.Sleep(10);
        //    int counter = 0;
        //    while (GetIO("Z", _stageIOPara._PinDown) || !GetIO("Z", _stageIOPara._PinUp))
        //    {
        //        Thread.Sleep(10);
        //        SetIO("Z", _stageIOPara._PinControl, true);
        //        counter++;
        //        if (counter > MAXNUM)
        //        {
        //            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
        //            RecordLog(error);
        //            throw new Exception(error);
        //        }// return false;
        //    }
        //    if (!GetIO("Z", _stageIOPara._PinDown) && GetIO("Z", _stageIOPara._PinUp))
        //        return true;
        //    else
        //    {
        //        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
        //        RecordLog(error);
        //        throw new Exception();
        //    }//return false;
        //}
        private bool UpPinFast()
        {
            if (IsPinUp())
                return true;
            string error;
            if (_WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
            {
                SetIO("Z", _stageIOPara._PinControl, false);
                SetIO("Z", _stageIOPara._PinControlDown, false);
                Thread.Sleep(100);
                SetIO("Z", _stageIOPara._PinControl, true);
                Thread.Sleep(10);
                int counter = 0;
                while (GetIO("Z", _stageIOPara._PinDown) || !GetIO("Z", _stageIOPara._PinUp))
                {
                    Thread.Sleep(10);
                    SetIO("Z", _stageIOPara._PinControl, true);
                    counter++;
                    if (counter > MAXNUM)
                    {
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                        else
                            error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }// return false;
                }
                if (!GetIO("Z", _stageIOPara._PinDown) && GetIO("Z", _stageIOPara._PinUp))
                    return true;
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                    else
                        error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                    RecordLog(error);
                    throw new Exception();
                }//return false;
            }
            else if(_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck) 
            {
                SetIO("Z", _stageIOPara._PinControl, true);
                Thread.Sleep(10);
                int counter = 0;
                while (GetIO("Z", _stageIOPara._PinDown) || !GetIO("Z", _stageIOPara._PinUp))
                {
                    Thread.Sleep(10);
                    SetIO("Z", _stageIOPara._PinControl, true);
                    counter++;
                    if (counter > MAXNUM)
                    {
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                        else
                            error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }// return false;
                }
                if (!GetIO("Z", _stageIOPara._PinDown) && GetIO("Z", _stageIOPara._PinUp))
                    return true;
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                    else
                        error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                    RecordLog(error);
                    throw new Exception();
                }//return false;
            }
            else 
            {
                if (_languageMode == LanguageMode.EN)
                    error = "The lifting method for the wafer has not been configured correctly";
                else
                    error = "晶圆升降方式没有正确设置";
                RecordLog(error);
                throw new Exception(error);
            }
        }
        public bool IsPinControlEnable()
        {
            return GetIOOut("Z", _stageIOPara._PinControl);
        }
        const int MAXNUM = 100;
        //public bool DownPin()
        //{
        //    if (IsPinDown())
        //        return true;
        //    string error;
        //    SetIO("Z", _stageIOPara._PinControl, false);
        //    Thread.Sleep(10);
        //    int counter = 0;
        //    while (!GetIO("Z", _stageIOPara._PinDown) || GetIO("Z", _stageIOPara._PinUp))
        //    {
        //        Thread.Sleep(10);
        //        SetIO("Z", _stageIOPara._PinControl, false);
        //        counter++;
        //        if (counter > MAXNUM)
        //        {
        //            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
        //            RecordLog(error);
        //            throw new Exception(error);
        //        }//return false;
        //    }
        //    if (GetIO("Z", _stageIOPara._PinDown) && !GetIO("Z", _stageIOPara._PinUp))
        //    {
        //        if (IsWaferExist())
        //        {
        //            if (!Fix())
        //            {
        //                error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault];
        //                RecordLog(error);
        //                throw new Exception(error);
        //            }
        //        }
        //        return true;
        //    }
        //    else
        //    {
        //        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
        //        RecordLog(error);
        //        throw new Exception(error);
        //    }//return false;
        //}
        public bool DownPin()
        {
            if (IsPinDown())
                return true;
            string error;
            if (_WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
            {
                SetIO("Z", _stageIOPara._PinControl, false);
                SetIO("Z", _stageIOPara._PinControlDown, false);
                Thread.Sleep(100);
                SetIO("Z", _stageIOPara._PinControlDown, true);
                Thread.Sleep(10);
                int counter = 0;
                while (!GetIO("Z", _stageIOPara._PinDown) || GetIO("Z", _stageIOPara._PinUp))
                {
                    Thread.Sleep(10);
                    if(_WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
                        SetIO("Z", _stageIOPara._PinControlDown, true);
                    else if(_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck) 
                    {
                        SetIO("Z", _stageIOPara._PinControl, false);
                    }
                    else {; }
                    counter++;  
                    if (counter > MAXNUM)
                    {
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                        else
                            error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }//return false;
                }
                if (GetIO("Z", _stageIOPara._PinDown) && !GetIO("Z", _stageIOPara._PinUp))
                {
                    if (IsWaferExist())
                    {
                        if (!Fix())
                        {
                            if (_languageMode == LanguageMode.EN)
                                error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault];
                            else
                                error = StageErrorInfoZ.晶圆吸附故障.ToString();
                            RecordLog(error);
                            throw new Exception(error);
                        }
                    }
                    return true;
                }
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                    else
                        error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                    RecordLog(error);
                    throw new Exception(error);
                }//return false;
            }
            else if (_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck)
            {
                SetIO("Z", _stageIOPara._PinControl, false);
                Thread.Sleep(10);
                int counter = 0;
                while (!GetIO("Z", _stageIOPara._PinDown) || GetIO("Z", _stageIOPara._PinUp))
                {
                    Thread.Sleep(10);
                    SetIO("Z", _stageIOPara._PinControl, false);
                    counter++;
                    if (counter > MAXNUM)
                    {
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                        else
                            error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }//return false;
                }
                if (GetIO("Z", _stageIOPara._PinDown) && !GetIO("Z", _stageIOPara._PinUp))
                {
                    if (IsWaferExist())
                    {
                        if (!Fix())
                        {
                            if (_languageMode == LanguageMode.EN)
                                error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault];
                            else
                                error = StageErrorInfoZ.晶圆吸附故障.ToString();
                            RecordLog(error);
                            throw new Exception(error);
                        }
                    }
                    return true;
                }
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault];
                    else
                        error = StageErrorInfoZ.晶圆支撑升降故障.ToString();
                    RecordLog(error);
                    throw new Exception(error);
                }//return false;
            }
            else 
            {
                if (_languageMode == LanguageMode.EN)
                    error = "The lifting method for the wafer has not been configured correctly";
                else
                    error = "晶圆升降方式设置错误";
                RecordLog(error);
                throw new Exception(error);
            }
        }
        const double ZVMAX = 200;
        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        public bool UpChuck(double pos = 0, double Velocity1 = 10, double Velocity2 = 10)
        {
            bool hasLock = false;
            try
            {
                if (Velocity1 > ZVMAX)
                {
                    string error = $"UpChuck Z Velocity:{Velocity1} > ZVMAX:{ZVMAX}";
                    throw new Exception(error);
                }
                if (Velocity2 > ZVMAX)
                {
                    string error = $"UpChuck Z Velocity:{Velocity2} > ZVMAX:{ZVMAX}";
                    throw new Exception(error);
                }
                if (!CheckInitalPrepareState())
                {
                    return false;
                }
                if (!IsEFEMInterLockOutEnable())
                {
                    //if (IsOnLoadPos())
                    //    SetEFEMInterLockIn(true);
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                    else
                        throw new Exception(StageErrorInfoZ.触发EFEM互锁.ToString());
                }
               // if (Monitor.TryEnter(_mux, 30000))
               // {
                    hasLock = true;
                    //判断是否在装载位置
                    double[] aXYZPosition = new double[3] { 0, 0, 0 };
                    StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);

                    aXYZPosition[0] = result.Axis[AxisStatusItem.PositionFeedback, "X"].Value;
                    aXYZPosition[1] = result.Axis[AxisStatusItem.PositionFeedback, "Z"].Value;
                    aXYZPosition[2] = result.Axis[AxisStatusItem.PositionFeedback, "Theta"].Value;
                    //判断不在上下料位置则需要防呆处理
                    if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZInspecPos) < 0.1)
                    {
                        if (IsWaferExist())
                        {
                            if (!Fix())
                                return false;
                        }
                        //MoveAxis("Z", _stageRunPara._ZLoadPos, 50);
                        return true;
                    }
                    if (aXYZPosition[1] < _stageRunPara._ZUpToPinPos)
                    {
                        SetIO("Z", _stageIOPara._Fix, false);//预先打开真空吸附
                        if (MoveToZ(_stageRunPara._ZUpToPinPos, _stageRunPara._ZUpToPinVel1))
                        {
                            Fix();
                            MoveToZ(_stageRunPara._ZInspecPos, _stageRunPara._ZUpToPinVel2);
                        }
                        else
                        {
                            string error;
                            if (_languageMode == LanguageMode.EN)
                                error = "UpChuck Move Z Fault";
                            else
                                error = "升Chuck移动Z轴故障";
                            RecordLog(error);
                            throw new Exception();
                        }
                    }
                    else if ((aXYZPosition[1] > _stageRunPara._ZUpToPinPos)
                        && (aXYZPosition[1] < _stageRunPara._ZInspecPos))
                    {
                        Fix();
                        MoveToZ(_stageRunPara._ZInspecPos, _stageRunPara._ZUpToPinVel2);
                    }
                    else {; }

               // }
                //else
                //{
                //    string error;
                //    if (_languageMode == LanguageMode.EN)
                //        error = "Wait Enter UpChuck Time Out";
                //    else
                //        error = "等待进入升Chuck超时";
                //    RecordLog(error);
                //    throw new Exception();
                //}
                return true;
            }
            catch (Exception ex)
            {
                throw ex;
            }
            //finally { if (hasLock) Monitor.Exit(_mux); }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="pos"></param>
        /// <param name="Velocity1"></param>
        /// <param name="Velocity2"></param>
        /// <returns></returns>
        public bool DownChuck(double pos = 0, double Velocity1 = 10, double Velocity2 = 10)
        {
            bool hasLock = false;
            try
            {
                if (Velocity1 > ZVMAX)
                {
                    string error = $"UpChuck Z Velocity:{Velocity1} > ZVMAX:{ZVMAX}";
                    throw new Exception(error);
                }
                if (Velocity2 > ZVMAX)
                {
                    string error = $"UpChuck Z Velocity:{Velocity2} > ZVMAX:{ZVMAX}";
                    throw new Exception(error);
                }
                if (!CheckInitalPrepareState())
                {
                    return false;
                }
                if (!IsEFEMInterLockOutEnable())
                {
                    //if (IsOnLoadPos())
                    //    SetEFEMInterLockIn(true);
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                    else
                        throw new Exception(StageErrorInfoZ.触发EFEM互锁.ToString());
                }
                //if (Monitor.TryEnter(_mux, 30000))
                // {
                    hasLock = true;
                    //判断是否在避让位置
                    //if (isPinInAvoidPos()) 
                    //{
                    //    //Z轴升高至聚焦高度让PIN能够避开Wafer进入支撑位置
                    //    MoveToZ(_stageRunPara._ZInspecPos, _stageRunPara._ZUpToPinVel2);
                    //    ChangePinPosWithInitAvoidance(false);
                    //}

                    //判断是否在装载位置
                    double[] aXYZPosition = new double[3] { 0, 0, 0 };
                    StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);

                    aXYZPosition[0] = result.Axis[AxisStatusItem.PositionFeedback, "X"].Value;
                    aXYZPosition[1] = result.Axis[AxisStatusItem.PositionFeedback, "Z"].Value;
                    aXYZPosition[2] = result.Axis[AxisStatusItem.PositionFeedback, "Theta"].Value;

                    if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) < 0.1)
                    {
                        if (IsWaferExist())
                        {
                            if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPin)
                            {
                                if (isPinInAvoidPos())
                                {
                                    MoveToZ(_stageRunPara._ZInspecPos, _stageRunPara._ZUpToPinVel2);
                                    ChangePinPosWithInitAvoidance(false);
                                    MoveToZ(_stageRunPara._ZDownToPinPos, _stageRunPara._ZDownToPinVel1);
                                }
                            }

                            Release();
                            MoveToZ(_stageRunPara._ZLoadPos, _stageRunPara._ZDownToPinVel2);

                        }
                        else
                        {
                            if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPin)
                            {
                                //判断是否移动到支撑位
                                if (isPinInAvoidPos())
                                {
                                    ChangePinPosWithInitAvoidance(false);
                                }
                            }
                        }
                        return true;
                    }
                    else if (aXYZPosition[1] > _stageRunPara._ZDownToPinPos)
                    {
                        if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPin)
                        {
                            //并行移动
                            ChangePinPosWithInitAvoidance(false, false);
                        }
                        if (MoveToZ(_stageRunPara._ZDownToPinPos, _stageRunPara._ZDownToPinVel1))
                        {
                            if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPin)
                            {
                                //判断是否移动到支撑位
                                if (isPinInAvoidPos())
                                {
                                    ChangePinPosWithInitAvoidance(false);
                                }
                            }
                            Release();
                            MoveToZ(_stageRunPara._ZLoadPos, _stageRunPara._ZDownToPinVel2);
                        }
                        else
                        {
                            string error;
                            if (_languageMode == LanguageMode.EN)
                                error = "Down Chuck Move Z Fault";
                            else
                                error = "降Chuck移动Z轴故障";
                            RecordLog(error);
                            throw new Exception(error);
                        }
                    }
                    else if ((aXYZPosition[1] < _stageRunPara._ZDownToPinPos)
                        && (aXYZPosition[1] > _stageRunPara._ZLoadPos))
                    {
                        if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPin)
                        {
                            if (isPinInAvoidPos())
                            {
                                MoveToZ(_stageRunPara._ZInspecPos, _stageRunPara._ZUpToPinVel2);
                                ChangePinPosWithInitAvoidance(false);
                                MoveToZ(_stageRunPara._ZDownToPinPos, _stageRunPara._ZDownToPinVel1);
                            }
                        }

                        Release();
                        MoveToZ(_stageRunPara._ZLoadPos, _stageRunPara._ZDownToPinVel2);
                    }
                return true;
            }
            catch (Exception ex)
            {
                throw ex;
            }
            //finally { if (hasLock) Monitor.Exit(_mux); }
        }

        /// <summary>
        /// 加载控制器内的脚本
        /// </summary>
        /// <param name="script"></param>
        const int TimeOut = 120 * 60 * 1000 / 100;
        public void RunScript(string script)
        {
            string error;
            try
            {
                SaveAFData();
                // if (!Directory.Exists(script))
                //     throw new Exception($"{script}不存在，请核实！");
                _controller.Runtime.Tasks[1].Program.Run(script);
                _runFlag = true;
                int timeCount = 1;
                while (_controller.Runtime.Tasks[1].Status.TaskState != TaskState.ProgramComplete)
                {
                    Thread.Sleep(100);
                    if (++timeCount > TimeOut) // 超时
                    {
                        _controller.Runtime.Tasks[1].Program.Stop();
                        if (_languageMode == LanguageMode.EN)
                            error = "StageScanTimeOut";
                        else
                            error = "Stage扫描超时";
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    if (_controller.Runtime.Tasks[1].Status.TaskState == TaskState.Error
                        || _controller.Runtime.Tasks[1].Status.TaskState == TaskState.Inactive
                        || _controller.Runtime.Tasks[1].Status.TaskState == TaskState.Idle)
                    {
                        _runFlag = false;
                        if(_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageScanFault] + "_" + _controller.Runtime.Tasks[1].Status.TaskState.ToString();
                        else
                            error = StageErrorInfoZ.Stage扫描故障.ToString() + "_" + _controller.Runtime.Tasks[1].Status.TaskState.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);
                    AxisFault t = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "Theta"].Value;
                    if (t != AxisFault.None)
                    {
                        _controller.Runtime.Tasks[1].Program.Stop();
                        throw new Exception(t.ToString());
                    }
                    AxisFault x = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "X"].Value;
                    if (x != AxisFault.None)
                    {
                        _controller.Runtime.Tasks[1].Program.Stop();
                        throw new Exception(x.ToString());
                    }
                    AxisFault z = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "Z"].Value;
                    if (z != AxisFault.None)
                    {
                        _controller.Runtime.Tasks[1].Program.Stop();
                        throw new Exception(z.ToString());
                    }
                }
                SetStageGlobleI((int)GlobalinfoI.gConcurrence, 0);
                if (getStage() != (int)StageErrorInfoE.Normal && getStage() < StageErrorInfoEE.StageErrorInfos.Count())
                {
                    SetStageGlobleI((int)GlobalinfoI.gConcurrence, 0);
                    _runFlag = false;
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoEE.StageErrorInfos[getStage()];
                    else
                    {
                        StageErrorInfoZ tem = (StageErrorInfoZ)(getStage());
                        error = tem.ToString();
                    }
                        
                    RecordLog(error);
                    throw new Exception(error);
                }
                _controller.Runtime.Tasks[1].Program.Stop();
                _runFlag = false;
            }
            catch (Exception ex)
            {
                _controller.Runtime.Tasks[1].Program.Stop();
                ResetState();
                Trace.WriteLine(ex.Message);
                string messageFault = string.Empty;
                StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);
                AxisFault t = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "Theta"].Value;
                if (t != AxisFault.None)
                {
                    messageFault += " ThetaAxis: " + t.ToString();
                }
                AxisFault x = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "X"].Value;
                if (x != AxisFault.None)
                {
                    messageFault += " XAxis: " + x.ToString();
                }
                AxisFault z = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "Z"].Value;
                if (z != AxisFault.None)
                {
                    messageFault += " ZAxis: " + z.ToString();
                }
                error = ex.Message + messageFault;
                RecordLog(error);
                throw new Exception(ex.Message + messageFault);
            }
        }
        private void RunConcurrence()
        {
            try
            {
                if (_controller.Runtime.Tasks[2].Status.TaskState != TaskState.Idle
                    || _controller.Runtime.Tasks[2].Status.TaskState != TaskState.ProgramComplete)
                {
                    _controller.Runtime.Tasks[2].Program.Stop();
                }
                _controller.Runtime.Tasks[2].Program.Run(_stageRunPara._StageConcurrencePath);

            }
            catch (Exception ex)
            {
                RecordLog(ex.Message);
                throw ex;
            }
        }
        /*public void Run()
        {
            if (_loadRecParaFlag)
            {
                if (_recParaChange)
                {
                    SetStageRunParaGlobal();
                    _recParaChange = false;
                }
                RunScript(Path.GetFileName(_stageRunPara._SprialScriptPath));
            }
            else
            {
                ResetState();
                throw new Exception("NotLoadStageRecipe!");
            }


        }*/
        public void Run()
        {
            if (!CheckInitalPrepareState())
            {
                return;
            }
            if (!IsEFEMInterLockOutEnable())
            {
                //if (IsOnLoadPos())
                //    SetEFEMInterLockIn(true);
                if (_languageMode == LanguageMode.EN)
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                else
                    throw new Exception(StageErrorInfoZ.触发EFEM互锁.ToString());
                //return false;
            }
            SetEFEMInterLockIn(false);
            //关门
            CloseInspectDoor(false);

            if (_loadRecParaFlag)
            {
                SetIO("Z", _stageIOPara._SpiralRunFlag, false);
                if (Math.Abs(GetStageGlobleR((int)GlobalInfo.gCircleAngleStart)) > 0 && !_recParaChange)
                {
                    SetStageRunParaGlobal();
                    if(_stageRunPara._AFControlFlag > 0)
                        SetStageGlobleR((int)GlobalInfo.gZinspect, _stageRunPara._ZInspecPos - _AFZOffset);
                }
                else
                {
                    SetStageRunParaGlobal();
                    if (_stageRunPara._AFControlFlag > 0)
                        SetStageGlobleR((int)GlobalInfo.gZinspect, _stageRunPara._ZInspecPos - _AFZOffset);
                    _recParaChange = false;
                    //设置PLC OFF
                    SetStageGlobleI((int)GlobalinfoI.gPLCControl, 1);
                    SetStageGlobleI((int)GlobalinfoI.gBFCalControl, 0);
                    SetStageGlobleI((int)GlobalinfoI.gConcurrence, 0);
                    if (IsWaferExist())
                    {
                        SetStageGlobleI((int)GlobalinfoI.gScanWithWafer, 1);
                    }
                    else
                    {
                        SetStageGlobleI((int)GlobalinfoI.gScanWithWafer, 0);
                    }
                    RunScript(Path.GetFileName(_stageRunPara._SprialScriptPath));

                }
                SetStageGlobleI((int)GlobalinfoI.gConcurrence, 1);
                SetStageGlobleI((int)GlobalinfoI.gScanWithWafer, 1);
                SetStageGlobleI((int)GlobalinfoI.gScanWithWafer, _stageRunPara._SpiralWithWaferFlag);
                SetStageGlobleI((int)GlobalinfoI.gPLCControl, 0);
                SetStageGlobleI((int)GlobalinfoI.gBFCalControl, 0);
                SetStageGlobleI((int)GlobalinfoI.gStopInspectAF, 0);
                Thread.Sleep(50);
                if (_stageRunPara._AFControlFlag > 0)
                {
                    RunConcurrence();
                }
                RunScript(Path.GetFileName(_stageRunPara._SprialScriptPath));
            }
            else
            {
                ResetState();
                string error;
                if (_languageMode == LanguageMode.EN)
                    error = "NotLoadStageScanScript";
                else
                    error = "没有加载Stage扫描脚本";
                RecordLog(error);
                throw new Exception(error);
            }
        }
        public void BFCalibration()
        {
            if (_loadRecParaFlag)
            {
                SetStageRunParaGlobal();
                _recParaChange = true;

                if (IsWaferExist())
                {
                    SetStageGlobleI((int)GlobalinfoI.gScanWithWafer, 1);
                }
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("NotFindWaferOnChuck!");
                    else
                        throw new Exception("Chuck上没有发现晶圆");
                }
                SetStageGlobleI((int)GlobalinfoI.gBFCalControl, 1);
                RunScript(Path.GetFileName(_stageRunPara._SprialScriptPath));
                SetStageGlobleI((int)GlobalinfoI.gBFCalControl, 0);
                ResetState();
                _recParaChange = true;
            }
            else
            {
                _recParaChange = true;
                ResetState();
                if (_languageMode == LanguageMode.EN)
                    throw new Exception("NotLoadStageRecipe!");
                else
                    throw new Exception("没有加载Stage扫描配方");
            }
        }
        /// <summary>
        ///  //读取配置文件或者全局变量
        /// </summary>
        private void UpdateStageRunPara()
        {
            try
            {
                _stageRunPara._SensorToOriginal = -91.797;
                _stageRunPara._SprialScriptPath = "D:\\F3000\\AKStage.ascript";//"E:\\Aerotech\\AKStage.ascript";
                _stageRunPara._ZInspecPos = 12.073;
                _stageRunPara._Fov = 2;
                _stageRunPara._WaferWaferRadius = 154;
                _stageRunPara._PixelSize = 0.0006;
                _stageRunPara._Binning = 8;
                //_stageRunPara._CameraLR = 650000;
                _stageRunPara._TLoadPos = -92.05066;//-31.75478;//28.43478;
                _stageRunPara._XLoadPos = 0.0;
                _stageRunPara._ZLoadPos = -5.0;
                _stageRunPara._CircleNum = 9;
                _stageRunPara._SpiralWithWaferFlag = 0;
                _stageRunPara._AFControlFlag = 0;
                //IO配值脚本暂时写死，不用上层配置
                // if (!Directory.Exists(_stageRunPara._sprialScriptPath))
                //     throw new Exception($"{_stageRunPara._sprialScriptPath}不存在，请核实！");
                //uploadFileToController(_stageRunPara._SprialScriptPath);
                _loadParaFlag = true;
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                Trace.WriteLine(ex.Message);
            }
        }
        /// <summary>
        /// 读取配置文件或者全局变量
        /// </summary>
        private void UpdateStageIOPara()
        {
            _stageIOPara._Fix = 6;
            _stageIOPara._PinDown = 2;
            _stageIOPara._PinUp = 3;
            _stageIOPara._TairPressure = 4;
            _stageIOPara._WaferExist = 0;
            _stageIOPara._PinControl = 0;
            _stageIOPara._VacPressure = 7;
            _stageIOPara._SpiralRunFlag = 7;
            _stageIOPara._AFLightControl = 1;
            _stageIOPara._PinControlDown = 2;

            _stageIOPara._AFVIO = 0;
            _stageIOPara._EFEMInterLokcIn = 3;
            _stageIOPara._EFEMInterLockOut = 5;

            _stageIOPara._InspectDoorOpen = 1;
            _stageIOPara._InspectDoorClose = 6;

            _stageIOPara._InspectDoorOpenControl = 4;
            _stageIOPara._InspectDoorCloseControl = 5;

            _stageIOPara._PinWithSizePosSmall = 0;
            _stageIOPara._PinWithSizePosBig = 1;
            _stageIOPara._PinAvoidZInitPos = 3;
            _stageIOPara._PinNormalPos = 2;
            //_stageIOPara._PinWithSizePosChangeControl = 5;
            //_stageIOPara._PinAvoidZInitPosChangeControl = 6;
            //_stageIOPara._PinAvoidZInitPosChangeControl = 6;
            _stageIOPara._PinWithSizePosChangeSmallControl = 0;
            _stageIOPara._PinWithSizePosChangeBigControl = 1;
            _stageIOPara._PinNormalPosChangeControl = 2;
            _stageIOPara._PinAvoidPosChangeControl = 3;

            _stageIOPara._BigWaferExist = 0;//等待确认

        }
        private void SetStageRunParaGlobal()
        {
            _stageRunPara._SprialScriptPath = "D:\\F3000\\AKStage.ascript";//"E:\\Aerotech\\AKStage.ascript";

            if (_stageRunPara._WaferSize == 8) {
                //SetStageGlobleR((int)GlobalInfo.gFOV, _Fovs[1]);

                SetStageGlobleR((int)GlobalInfo.gWaferWaferRadius, _ScanRadius[1]);
                // SetStageGlobleI((int)GlobalInfo.gCircleNum, 4);
                //SetStageGlobleR((int)GlobalInfo.gPixelSize, FPixelSizes.FDF8);

                //SetStageGlobleR((int)GlobalInfo.gPixelCount, FPixelCount.FDF8);

                _stageRunPara._WaferWaferRadius = _ScanRadius[1];
                // _stageRunPara._Fov = _Fovs[1];
            }
            else if (_stageRunPara._WaferSize == 12)
            {
                //SetStageGlobleR((int)GlobalInfo.gFOV, _Fovs[2]);
                
                SetStageGlobleR((int)GlobalInfo.gWaferWaferRadius, _ScanRadius[2]);
                // SetStageGlobleI((int)GlobalInfo.gCircleNum, 9);
                // SetStageGlobleR((int)GlobalInfo.gPixelSize, FPixelSizes.FDF112);

                //SetStageGlobleR((int)GlobalInfo.gPixelCount, FPixelCount.FDF8);
               
                _stageRunPara._WaferWaferRadius = _ScanRadius[2];
                //_stageRunPara._Fov = _Fovs[2];
            }
            else if (_stageRunPara._WaferSize == 6)
            {
                //SetStageGlobleR((int)GlobalInfo.gFOV, _Fovs[2]);

                SetStageGlobleR((int)GlobalInfo.gWaferWaferRadius, _ScanRadius[0]);
                // SetStageGlobleI((int)GlobalInfo.gCircleNum, 4);
                // SetStageGlobleR((int)GlobalInfo.gPixelSize, FPixelSizes.FDF112);

                //SetStageGlobleR((int)GlobalInfo.gPixelCount, FPixelCount.FDF8);

                _stageRunPara._WaferWaferRadius = _ScanRadius[0];
                //_stageRunPara._Fov = _Fovs[2];
            }
            else;
            SetStageGlobleR((int)GlobalInfo.gSensorToOriginal, _stageRunPara._SensorToOriginal);

            SetStageGlobleR((int)GlobalInfo.gFOV, _stageRunPara._Fov);
            SetStageGlobleR((int)GlobalInfo.gPixelSize, _stageRunPara._PixelSize);
            SetStageGlobleR((int)GlobalInfo.gPixelCount, _stageRunPara._PixelCount);
            SetStageGlobleI((int)GlobalInfo.gCircleNum, _stageRunPara._CircleNum);

            if (_stageRunPara._ScanGrade == (int)FScanGrade.FScanHSpeed)
            {
                // SetStageGlobleR((int)GlobalInfo.gCameraLR, _BinFreqsFor8[2].Item2);
                // SetStageGlobleR((int)GlobalInfo.gBinning, _BinFreqsFor8[2].Item1);
            }
            else if (_stageRunPara._ScanGrade == (int)FScanGrade.FScanStandard)
            {
                // SetStageGlobleR((int)GlobalInfo.gCameraLR, _BinFreqsFor8[0].Item2);
                // SetStageGlobleR((int)GlobalInfo.gBinning, _BinFreqsFor8[0].Item1);
            }
            else if (_stageRunPara._ScanGrade == (int)FScanGrade.FScanHPrecision)
            {
                //   SetStageGlobleR((int)GlobalInfo.gCameraLR, _BinFreqsFor8[1].Item2);
                //   SetStageGlobleR((int)GlobalInfo.gBinning, _BinFreqsFor8[1].Item1);
            }
            else;
            SetStageGlobleR((int)GlobalInfo.gCameraLR, _stageRunPara._CameraLR);
            SetStageGlobleR((int)GlobalInfo.gBinning, _stageRunPara._Binning);

            //SetStageGlobleR((int)GlobalInfo.gCameraLR, _stageRunPara._CameraLR);
            SetStageGlobleR((int)GlobalInfo.gZinspect, _stageRunPara._ZInspecPos);
            SetStageGlobleR((int)GlobalInfo.gXstart, _stageRunPara._XLoadPos);
            SetStageGlobleR((int)GlobalInfo.gZstart, _stageRunPara._ZLoadPos);
            SetStageGlobleR((int)GlobalInfo.gTstart, _stageRunPara._TLoadPos);
            SetStageGlobleR((int)GlobalInfo.gZDownPos, _stageRunPara._ZDownToPinPos);
            SetStageGlobleR((int)GlobalinfoI.gScanWithWafer, _stageRunPara._SpiralWithWaferFlag);
            //SetStageGlobleR((int)GlobalInfo.gCircleNum, _stageRunPara._CircleNum);
            SetStageGlobleI((int)GlobalinfoI.gAutofocus, _stageRunPara._AFControlFlag);
            //SetStageGlobleI((int)GlobalInfo.gAFV, _stageRunPara._AFVBase);
            SetStageGlobleR((int)GlobalInfo.gAFV, _stageRunPara._AFVBase + _stageRunPara._AFVOffset);
            SetStageGlobleR((int)GlobalInfo.gAFSumThreshold, _stageRunPara.AFSumThreshold);
            SetStageGlobleR((int)GlobalInfo.gTTriggerStartAngle, _stageRunPara._TTriggerStartAngle);
            SetStageGlobleI((int)GlobalinfoI.gStopDataSnap, _stageRunPara._APPDataSnapFlag);
        }
        private void SaveAFData() 
        {
            if (_stageRunPara._APPDataSaveFlag == 1)
            {
                if((_ScanCount >= _stageRunPara._ScanCountForAppData) 
                    &&(_stageRunPara._ScanCountForAppData > 0)
                    &&(_stageRunPara._APPDataSavePath != null)) 
                {
                    SetStageGlobleI((int)GlobalinfoI.gSaveAppData, 1);
                    SetStageGlobleStr((int)GlobalinfoStr.gAppSaveDataPath, _stageRunPara._APPDataSavePath);
                    _ScanCount = 0;
                }
                if (_stageRunPara._ScanCountForAppData <= 0 || _stageRunPara._APPDataSavePath == null)
                    ;
                else
                    _ScanCount++;
            }
            else 
            {
                SetStageGlobleI((int)GlobalinfoI.gSaveAppData, 0);
            }
        }
        private void SetStageIOPara()
        {
            SetStageGlobleI((int)GlobalinfoI.gAdsorbControlIO, _stageIOPara._Fix);
            SetStageGlobleI((int)GlobalinfoI.gPinControlIO, _stageIOPara._PinControl);
            SetStageGlobleI((int)GlobalinfoI.gPinDownPosIO, _stageIOPara._PinDown);
            SetStageGlobleI((int)GlobalinfoI.gPinUpPosIO, _stageIOPara._PinUp);
            SetStageGlobleI((int)GlobalinfoI.gAirIO, _stageIOPara._TairPressure);
            SetStageGlobleI((int)GlobalinfoI.gWaferIO, _stageIOPara._WaferExist);
            SetStageGlobleI((int)GlobalinfoI.gVacIO, _stageIOPara._VacPressure);
            SetStageGlobleI((int)GlobalinfoI.gAFLightControl, _stageIOPara._AFLightControl);
            //SetStageGlobleI((int)GlobalinfoI.gAutofocus, _stageIOPara._AFControl);
            SetStageGlobleI((int)GlobalinfoI.gSpiralStart, _stageIOPara._SpiralRunFlag);
        }
        /// <summary>
        /// 用于PLC频率设置不同的圈数对应不同的频率
        /// </summary>
        /// <returns></returns>
        private List<double> GetFres()
        {
            List<double> fres = new List<double>();
            fres.Add(GetStageGlobleR((int)GlobalInfo.gCircleFqStart));
            for (int i = 0; i < _stageRunPara._CircleNum; ++i)
            {
                fres.Add(GetStageGlobleR((int)GlobalInfo.gCircleFqStart) + i);
            }
            _triggleFres = fres;
            return fres;
        }
        /// <summary>
        /// 用于算法Remapping矫正
        /// </summary>
        /// <returns></returns>
        private List<double> GetAngles()
        {
            List<double> angles = new List<double>();

            for (int i = 0; i < _stageRunPara._CircleNum + 1; ++i)
            {
                angles.Add(GetStageGlobleR((int)GlobalInfo.gCircleAngleStart) + i);
            }
            _triggleAngles = angles;
            return angles;
        }
        private bool SetAngles(List<double> angs)
        {
            int num = angs.Count();
            if (num != _stageRunPara._CircleNum)
                return false;
            for (int i = 0; i < num; ++i)
            {
                SetStageGlobleR((int)GlobalInfo.gCircleAngleStart, angs[i]);
            }
            return true;
        }
        public bool GFix() 
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    return Fix(4);
                }
                else 
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                        error = "The current action of stage is in progress, Please wait";
                    else
                        error = "Stage当前动作正在进行中，请等待";
                    RecordLog(error);
                    throw new Exception(error);
                }
            }
            finally 
            {
                if(hasLock)
                    Monitor.Exit(_mux);
            }
        }
        public bool Fix()
        {
            if (_runFlag)
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception("Scanning in progress Please Wait");
                else
                    throw new Exception("扫描正在进行中，请等待");
            }
            //如何判断是否吸附成功
            //SetIO("Z", _outPutIOs[StageOutPutIO.Fix], true);
            //SetIO("Z", _stageIOPara._Fix, true);
            SetIO("Z", _stageIOPara._Fix, false);
            Thread.Sleep(10);
            int counter = 0;
            while (!GetIO("Z", _stageIOPara._VacPressure))
            {
                SetIO("Z", _stageIOPara._Fix, false);
                Thread.Sleep(10);
                counter++;
                if (counter > MAXNUM)
                    break;
            }
            if (counter > MAXNUM)//if (!GetIO("Z", _stageIOPara._VacPressure))
            {
                string error;
                if (_languageMode == LanguageMode.EN)
                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault];
                else
                    error = StageErrorInfoZ.晶圆吸附故障.ToString();
                RecordLog(error);
                throw new Exception(error);
            }
            return true;
        }
        private bool FixNotTimeOut()
        {
            try
            {
                if (_runFlag)
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Scanning in progress Please Wait");
                    else
                        throw new Exception("扫描正在进行中，请等待");
                }
                //如何判断是否吸附成功
                //SetIO("Z", _outPutIOs[StageOutPutIO.Fix], true);
                //SetIO("Z", _stageIOPara._Fix, true);
                SetIO("Z", _stageIOPara._Fix, false);
                Thread.Sleep(10);
                int counter = 0;
                while (!GetIO("Z", _stageIOPara._VacPressure))
                {
                    SetIO("Z", _stageIOPara._Fix, false);
                    Thread.Sleep(10);
                    counter++;
                    if (counter > 170)
                        return false;
                }
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool Fix(int taskID)
        {
            if (_runFlag)
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception("Scanning in progress Please Wait");
                else
                    throw new Exception("扫描正在进行中，请等待");
            }
            //如何判断是否吸附成功
            //SetIO("Z", _outPutIOs[StageOutPutIO.Fix], true);
            //SetIO("Z", _stageIOPara._Fix, true);
            SetIO("Z", _stageIOPara._Fix, false, taskID);
            Thread.Sleep(10);
            int counter = 0;
            while (!GetIO("Z", _stageIOPara._VacPressure, taskID))
            {
                SetIO("Z", _stageIOPara._Fix, false, taskID);
                Thread.Sleep(10);
                counter++;
                if (counter > MAXNUM)
                    break;
            }
            if (counter > MAXNUM)//if (!GetIO("Z", _stageIOPara._VacPressure))
            {
                string error;
                if (_languageMode == LanguageMode.EN)
                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault];
                else
                    error = StageErrorInfoZ.晶圆吸附故障.ToString();
                RecordLog(error);
                throw new Exception(error);
            }
            return true;
        }
        public bool GetAbsorbControlEnable()
        {
            return GetIOOut("Z", _stageIOPara._Fix);
        }
        public bool IsVacPressureOn() { return GetIO("Z", _stageIOPara._VacPressure); }
        public bool GRelease() 
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    return Release(4);
                }
                else
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                        error = "The current action of stage is in progress, Please wait";
                    else
                        error = "Stage当前动作正在进行中，请等待";
                    RecordLog(error);
                    throw new Exception(error);
                }
            }
            finally
            {
                if (hasLock)
                    Monitor.Exit(_mux);
            }
        }
        public bool Release()
        {
            if (_runFlag)
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception("Scanning in progress Please Wait");
                else
                    throw new Exception("扫描正在进行中，请等待");
            }
            //如何判断是否释放成功
            //SetIO("Z", _outPutIOs[StageOutPutIO.Release], true);
            //SetIO("Z", _stageIOPara._Fix, false);
            SetIO("Z", _stageIOPara._Fix, true);
            Thread.Sleep(10);
            int counter = 0;
            while (GetIO("Z", _stageIOPara._VacPressure))
            {
                SetIO("Z", _stageIOPara._Fix, true);
                Thread.Sleep(10);
                counter++;
                if (counter > MAXNUM)
                    break;
            }
            if (counter > MAXNUM)//if (GetIO("Z", _stageIOPara._VacPressure))
            {
                string error;
                if (_languageMode == LanguageMode.EN)
                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ReleaseWaferFault];
                else
                    error = StageErrorInfoZ.晶圆释放故障.ToString();
                RecordLog(error);
                throw new Exception(error);
            }//return false;
            return true;
        }
        public bool Release(int taskID)
        {
            if (_runFlag)
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception("Scanning in progress Please Wait");
                else
                    throw new Exception("扫描正在进行中，请等待");
            }
            //如何判断是否释放成功
            //SetIO("Z", _outPutIOs[StageOutPutIO.Release], true);
            //SetIO("Z", _stageIOPara._Fix, false);
            SetIO("Z", _stageIOPara._Fix, true, taskID);
            Thread.Sleep(10);
            int counter = 0;
            while (GetIO("Z", _stageIOPara._VacPressure, taskID))
            {
                SetIO("Z", _stageIOPara._Fix, true, taskID);
                Thread.Sleep(10);
                counter++;
                if (counter > MAXNUM)
                    break;
            }
            if (counter > MAXNUM)//if (GetIO("Z", _stageIOPara._VacPressure))
            {
                string error;
                if (_languageMode == LanguageMode.EN)
                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ReleaseWaferFault];
                else
                    error = StageErrorInfoZ.晶圆释放故障.ToString();
                RecordLog(error);
                throw new Exception(error);
            }//return false;
            return true;
        }
        public bool IsWaferExist()
        {
            //return GetIO("Z", _inPutIOs[StageInputIO.WaferExist]);
            try { return GetIO("Z", _stageIOPara._WaferExist); }
            catch(Exception e) 
            {
                RecordLog(e.Message);
                throw e;
            }
        }
        bool isBigWaferExist() 
        {
            try 
            { 
                return (GetIO("X", _stageIOPara._BigWaferExist) && GetIO("Z", _stageIOPara._WaferExist));
            }
            catch (Exception e)
            {
                RecordLog(e.Message);
                throw e;
            }
        }
        public bool IsAirPressureReady()
        {
            try { return GetIO("Z", _stageIOPara._TairPressure); }
            catch(Exception e) 
            {
                RecordLog(e.Message);
                throw e;
            }
        }
        private void Start()
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 10000))
                {
                    hasLock = true;
                    if (_controller != null)
                    {
                        _controller.Start();
                        Enable(new string[] { "X", "Z", "Theta" });
                    }
                }
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("WaitStageStartTimeOut");
                    else
                        throw new Exception("等待Stage启动超时");
                }
            }
            catch (Exception ex)
            {
                string sErrorMessage;
                if (_languageMode == LanguageMode.EN)
                    sErrorMessage = $"Start Stage Fail\r\n{ex.Message}\r\n{ex.StackTrace}";
                else
                    sErrorMessage = $"StartStage失败\r\n{ex.Message}\r\n{ex.StackTrace}";
                //MessageBox.Show(sErrorMessage);
                Trace.WriteLine(sErrorMessage);
                RecordLog(sErrorMessage.ToString());
                throw ex;
            }
            finally
            {
                if (hasLock) Monitor.Exit(_mux);
            }
        }
        private void Stop()
        {
            bool hasLock = true;
            try
            {
                if (Monitor.TryEnter(_mux, 10000))
                {
                    hasLock = true;
                    if (_controller != null)
                    {
                        _controller.Stop();
                        Disable(new string[] { "X", "Z", "Theta" });
                    }
                }
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("WaitStageStopTimeOut");
                    else
                        throw new Exception("等待Stage停止超时");
                }
            }
            catch (Exception ex)
            {
                string sErrorMessage = $"StopStageFault!\r\n{ex.Message}\r\n{ex.StackTrace}";
                MessageBox.Show(sErrorMessage);
                Trace.WriteLine(sErrorMessage);
            }
            finally
            {
                if (hasLock) Monitor.Exit(_mux);
            }
        }
        private void Reset()
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 20000))
                {
                    hasLock = true;
                    if (_controller != null)
                    {
                        _controller.Reset();
                    }
                }
                else 
                { 
                    if (_languageMode == LanguageMode.EN) 
                        throw new Exception("WaitStageResetTimeOut");
                    else 
                        throw new Exception("等待Stage重启超时");
                }
            }
            catch (Exception ex)
            {
                string sErrorMessage = $"ResetStageFault!\r\n{ex.Message}\r\n{ex.StackTrace}";
                MessageBox.Show(sErrorMessage);
                Trace.WriteLine(sErrorMessage);
            }
            finally { if (hasLock) Monitor.Exit(_mux); }
        }
        private void Abort()
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 10000))
                {
                    hasLock = true;
                    if (_controller != null)
                    {
                        string[] axiss = new string[3] { "X", "Z", "Theta" };
                        _controller.Runtime.Commands.Motion.Abort(axiss);
                        WaitMotionDone(axiss);
                    }
                }else { throw new Exception("WaitStageAbortTimeOut"); }
            }
            catch (Exception ex)
            {
                string sErrorMessage = $"ResetStage失败!\r\n{ex.Message}\r\n{ex.StackTrace}";
                MessageBox.Show(sErrorMessage);
                Trace.WriteLine(sErrorMessage);
            }
            finally { if(hasLock) Monitor.Exit(_mux); }
        }
        public bool IsPinUp()
        {
            if (GetIO("Z", _stageIOPara._PinUp) && !GetIO("Z", _stageIOPara._PinDown))
                return true;
            else
                return false;
        }
        public bool IsPinDown()
        {
            if (GetIO("Z", _stageIOPara._PinDown) && GetIO("Z", _stageIOPara._PinUp))
                return true;
            else
                return false;
        }
        private bool Home()
        {
            //注意Z轴要向下寻零，向上会与镜头干涉
            ClearException();
            bool hasLock = true;
            try
            {
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    //有料需要吸附再回零
                    if (IsWaferExist())
                    {
                        //SetIO("Z", _stageIOPara._Fix, true);
                        SetIO("Z", _stageIOPara._Fix, false);
                        if (_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck
                            || _WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
                        {
                            //判断PIN是否升起，升起需要降落，防止干涉
                            if (IsPinUp())
                            {
                                DownPin();
                            }
                            if (!Fix())
                                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault]);
                        }
                        
                        if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPin
                            || _WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPinNoAvoid) 
                        {
                            ;
                        }
                    }
                    else 
                    {
                        if (_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck
                            || _WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
                        {
                            //判断PIN是否升起，升起需要降落，防止干涉
                            if (IsPinUp())
                            {
                                DownPin();
                            }
                        }
                    }
                    //判断PIN是否升起，升起需要降落，防止干涉
                    //if (IsPinUp())
                    //{
                    //    DownPin();
                    //}
                    string[] axiss = new string[3] { "X", "Z", "Theta" };
                    _controller.Runtime.Commands.Motion.Home(axiss);

                    //_controller.Runtime.Commands.Motion.WaitForMotionDone(axiss);
                    WaitMotionDone(axiss);
                    return true;
                    //Z轴回零
                    //_controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                    //_controller.Runtime.Commands.Motion.MoveAbsolute("X", -90, 20);
                    // _controller.Runtime.Commands.Motion.WaitForMotionDone("X");
                    // _controller.Runtime.Commands.Motion.Home("Z");
                    // _controller.Runtime.Commands.Motion.WaitForMotionDone("Z");
                }
                else { throw new Exception("WaitStageHomeTimeOut"); }
            }
            catch (Exception ex)
            {
                string sErrorMessage = $"StageHome失败!\r\n{ex.Message}\r\n{ex.StackTrace}";
                //MessageBox.Show(sErrorMessage);
                Trace.WriteLine(sErrorMessage);
                throw ex;
            }
            finally { if(hasLock) Monitor.Exit(_mux); }
        }
        private void homeAxis(string axisName)
        {
            ClearException();
            if (!IsEFEMInterLockOutEnable())
            {
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
            }
            try
            {
                ////判断PIN是否升起，升起需要降落，防止干涉
                //if (IsPinUp())
                //{
                //    DownPin();
                //}
                //有料需要吸附再回零
                if (IsWaferExist())
                {
                    if (!Fix())
                        throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault]) ;
                }

                _controller.Runtime.Commands.Motion.Home(axisName);

                // _controller.Runtime.Commands.Motion.WaitForMotionDone(axisName);
                WaitMotionDone(axisName);
            }
            catch (Exception ex)
            {
                string sErrorMessage = $"StageHome失败!\r\n{ex.Message}\r\n{ex.StackTrace}";
                //MessageBox.Show(sErrorMessage);
                throw ex;
                //Trace.WriteLine(sErrorMessage);
            }
        }
        public void HomeX() 
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 20000))
                {
                    hasLock = true;
                    homeAxis("X");
                }
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Wait Stage X Axis Home Time Out");
                    else
                        throw new Exception("Stage X轴回零超时");
                }
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
            finally { if (hasLock) Monitor.Exit(_mux); }
        }
        public void HomeT()
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 20000))
                {
                    hasLock = true;
                    homeAxis("Theta");
                }
                else
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Wait Stage T Axis Home Time Out");
                    else
                        throw new Exception("Stage T轴回零超时");
                }
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
            finally { if (hasLock) Monitor.Exit(_mux); }
        }
        public void HomeZ()
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 20000))
                {
                    hasLock = true;
                    homeAxis("Z");
                }
                else 
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Wait Stage Z Axis Home Time Out");
                    else
                        throw new Exception("Stage Z轴回零超时");
                }
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
            finally { if (hasLock) Monitor.Exit(_mux); }
        }
        private void SetIO(string axisName, long output, bool value)
        {
            try { lock (_IOLock) { _controller.Runtime.Commands.IO.DigitalOutputSet(axisName, output, value ? 1 : 0, _StageTaskId); } }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        private void SetIO(string axisName, long output, bool value, int taskID)
        {
            try { lock (_GIOLock) { _controller.Runtime.Commands.IO.DigitalOutputSet(axisName, output, value ? 1 : 0, taskID); } }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        private bool GetIO(string axisName, long input)
        {
            try
            {
                long rValue;
                lock (_IOLock)
                {
                    rValue = _controller.Runtime.Commands.IO.DigitalInputGet(axisName, input, _StageTaskId);
                }
                return rValue > 0;
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        private bool GetIO(string axisName, long input, int taskID)
        {
            try
            {
                long rValue;
                lock (_GIOLock)
                {
                    rValue = _controller.Runtime.Commands.IO.DigitalInputGet(axisName, input, taskID);
                }
                return rValue > 0;
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        private bool GetIOOut(string axisName, long input)
        {
            try
            {
                long rValue;
                lock (_IOLock)
                {
                    rValue = _controller.Runtime.Commands.IO.DigitalOutputGet(axisName, input, _StageTaskId);
                }
                return rValue > 0;
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        private bool GetIOOut(string axisName, long input, int taskID)
        {
            try
            {
                long rValue;
                lock (_GIOLock)
                {
                    rValue = _controller.Runtime.Commands.IO.DigitalOutputGet(axisName, input, taskID);
                }
                return rValue > 0;
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        private void ClearException()
        {
            try { _controller.Runtime.Commands.FaultAndError.AcknowledgeAll(); } catch (Exception ex) { throw ex; }
        }
        public void EnableX() { try { _controller.Runtime.Commands.Motion.Enable("X"); } catch (Exception ex) { RecordLog(ex.Message); throw ex; } }
        public void EnableT() { try { _controller.Runtime.Commands.Motion.Enable("Theta"); } catch (Exception ex) { RecordLog(ex.Message); throw ex; } }
        public void EnableZ() { try { _controller.Runtime.Commands.Motion.Enable("Z"); } catch (Exception ex) { RecordLog(ex.Message); throw ex; } }
        public void DisableX() { try { _controller.Runtime.Commands.Motion.Disable("X"); } catch (Exception ex) { RecordLog(ex.Message); throw ex; } }
        public void DisableT() { try { _controller.Runtime.Commands.Motion.Disable("Theta"); } catch (Exception ex) { RecordLog(ex.Message); throw ex; } }
        public void DisableZ() { try { _controller.Runtime.Commands.Motion.Disable("Z"); } catch (Exception ex) { RecordLog(ex.Message); throw ex; } }

        private void EnableAll()
        {
            try { _controller.Runtime.Commands.Motion.Enable(new string[3] { "X", "Z", "Theta" }); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void DisableAll()
        {
            try { _controller.Runtime.Commands.Motion.Disable(new string[3] { "X", "Z", "Theta" }); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void Enable(string[] axisName)
        {
            try { _controller.Runtime.Commands.Motion.Enable(axisName); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void Disable(string[] axisName)
        {
            try { _controller.Runtime.Commands.Motion.Disable(axisName); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void SetStageGlobleI(int index, int value)
        {
            try { _controller.Runtime.Variables.Global.SetInteger(index, value); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private long GetStageGlobleI(int index)
        {
            try { return _controller.Runtime.Variables.Global.GetInteger(index); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void SetStageGlobleR(int index, double value)
        {
            try { _controller.Runtime.Variables.Global.SetReal(index, value); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private double GetStageGlobleR(int index)
        {
            try { return _controller.Runtime.Variables.Global.GetReal(index); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void SetStageGlobleIs(int startIndex, long[] values)
        {
            try { _controller.Runtime.Variables.Global.SetIntegers(startIndex, values); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private long[] GetStageGlobleIs(int startIndex, int num)
        {
            try { return _controller.Runtime.Variables.Global.GetIntegers(startIndex, num); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void SetStageGlobleRs(int startIndex, double[] values)
        {
            try { _controller.Runtime.Variables.Global.SetReals(startIndex, values); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private double[] GetStageGlobleRs(int startIndex, int num)
        {
            try { return _controller.Runtime.Variables.Global.GetReals(startIndex, num); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void SetStageGlobleStr(int index, string info)
        {
            try { _controller.Runtime.Variables.Global.SetString(index, info); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private string GetStageGlobleStr(int index)
        {
            try { return _controller.Runtime.Variables.Global.GetString(index); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private void SetStageGlobleStrs(int startIndex, string[] values)
        {
            try { _controller.Runtime.Variables.Global.SetStrings(startIndex, values); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private string[] GetStageGlobleStrs(int startIndex, int num)
        {
            try { return _controller.Runtime.Variables.Global.GetStrings(startIndex, num); } catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        /// <summary>
        /// 3轴并行运动，注意是否干涉
        /// </summary>
        private void MoveToXZT(string[] axisname, double[] pos, double[] speed)
        {
            try
            {
                _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                _controller.Runtime.Commands.Motion.MoveAbsolute(axisname, pos, speed);
                //_controller.Runtime.Commands.Motion.WaitForMotionDone(axisname);
                WaitMotionDone(axisname);
            }
            catch (Exception ex) { RecordLog(ex.Message); throw ex; };
        }
        private bool MoveToXZT(double fx = double.NaN, double ft = double.NaN, double fz = double.NaN)
        {
            //  ParamDevice paramDevice = GPICW.ParamDevice;
            //  ParamBFAOI paramBFAOI = GPICW.ParamBFAOI;
            //   paramBFAOI.MoveVelocity 需要区分X Theta Z
            try
            {
                if (_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck)
                {
                    if (IsPinUp())
                    {
                        if (!DownPin())
                        {
                            if (_languageMode == LanguageMode.EN)
                                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.WaferPinUpDownFault]);
                            else
                                throw new Exception(StageErrorInfoZ.晶圆支撑升降故障.ToString());
                        }
                    }
                }
                EnableAll();
                bool bx = double.IsNaN(fx);
                bool bt = double.IsNaN(ft);
                bool bz = double.IsNaN(fz);
                double[] pos = new double[] { fx, ft, fz };
                double[] speed = new double[] { };
                if (!bx && !bt && !bz)
                {
                    _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                    _controller.Runtime.Commands.Motion.MoveAbsolute(new string[] { "X", "Theta", "Z" }, pos, speed);
                    //_controller.Runtime.Commands.Motion.WaitForMotionDone(new string[] { "X", "Theta", "Z" });
                    WaitMotionDone(new string[] { "X", "Theta", "Z" });
                    return true;
                }
                return false;
            }
            catch (Exception e)
            {
                RecordLog(e.Message);
                throw e;
                MessageBox.Show(e.Message);
                Trace.WriteLine(e.Message);
                return false;
            }
        }
        public void MoveAxis(string axisname, double pos, double speed, bool wait = true)
        {
            try
            {
                if (!CheckInitalPrepareState())
                {
                    return;
                }
                //互锁

                if (!IsEFEMInterLockOutEnable())
                {
                    //if (IsOnLoadPos())
                    //    SetEFEMInterLockIn(true);
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                }
                if(_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck
                    ||_WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck) 
                {
                    if (IsWaferExist())
                    {
                        SetIO("Z", _stageIOPara._Fix, false);
                        if (!DownPin())
                        {
                            return;
                        }
                        if (!Fix())
                            throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault]);
                    }
                    if (!DownPin())
                    {
                        return;
                    }
                }
                _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                _controller.Runtime.Commands.Motion.MoveAbsolute(axisname, pos, speed);
                if (wait)
                {
                    // _controller.Runtime.Commands.Motion.WaitForMotionDone(axisname);
                    WaitMotionDone(axisname);
                }
            }
            catch (Exception e) { throw e; }
        }
        public void MoveAxisRelative(string axisname, double pos, double speed, bool wait = true)
        {
            try
            {
                if (!CheckInitalPrepareState())
                {
                    return;
                }
                //互锁

                if (!IsEFEMInterLockOutEnable())
                {
                    //if (IsOnLoadPos())
                    //    SetEFEMInterLockIn(true);
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                }
                if (_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck
                   || _WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
                {
                    if (IsWaferExist())
                    {
                        //SetIO("Z", _stageIOPara._Fix, true);
                        SetIO("Z", _stageIOPara._Fix, false);
                        if (!DownPin())
                        {
                            return;
                        }
                        if (!Fix())
                            throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault]);
                    }
                    if (!DownPin())
                    {
                        return;
                    }
                }
                _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Incremental);
                _controller.Runtime.Commands.Motion.MoveIncremental(axisname, pos, speed);
                if (wait)
                {
                    //_controller.Runtime.Commands.Motion.WaitForMotionDone(axisname);
                    WaitMotionDone(axisname);
                }
            }
            catch (Exception e) { throw e; }
        }

        public void MoveAxisJogPositive(string axisname)
        {
            try
            {
                if (!CheckInitalPrepareStateSingle())
                {
                    return;
                }
                //互锁

                if (!IsEFEMInterLockOutEnable())
                {
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                }
                if (_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck
                   || _WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
                {
                    if (IsWaferExist())
                    {
                        //SetIO("Z", _stageIOPara._Fix, true);
                        SetIO("Z", _stageIOPara._Fix, false);
                        if (!DownPin())
                        {
                            return;
                        }
                        if (!Fix())
                            throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault]);
                    }
                    if (!DownPin())
                    {
                        return;
                    }
                }
                double defaultAxisSpeed = _controllerParameters.Axes[axisname].Motion.DefaultAxisSpeed.Value;
                //_controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                _controller.Runtime.Commands.Motion.MoveFreerun(axisname, defaultAxisSpeed);
            }
            catch (Exception e) { throw e; }
        }
        public void MoveAxisJogNegative(string axisname)
        {
            try
            {
                if (!CheckInitalPrepareStateSingle())
                {
                    return;
                }
                //互锁

                if (!IsEFEMInterLockOutEnable())
                {
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                }
                if (_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck
                   || _WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
                {
                    if (IsWaferExist())
                    {
                        //SetIO("Z", _stageIOPara._Fix, true);
                        SetIO("Z", _stageIOPara._Fix, false);
                        if (!DownPin())
                        {
                            return;
                        }
                        if (!Fix())
                            throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.FixWaferFault]);
                    }
                    if (!DownPin())
                    {
                        return;
                    }
                }
                double defaultAxisSpeed = _controllerParameters.Axes[axisname].Motion.DefaultAxisSpeed.Value;
                //_controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                _controller.Runtime.Commands.Motion.MoveFreerun(axisname, -defaultAxisSpeed);
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public void MoveAxisJogStop(string axisname)
        {
            try
            {
                _controller.Runtime.Commands.Motion.MoveFreerunStop(axisname);
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public double GetAxisPos(string axisname)
        {
            try
            {
                StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);
                return result.Axis[AxisStatusItem.PositionFeedback, axisname].Value;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        private void MoveAxisInc(string axisname, double pos, double speed)
        {
            try
            {
                _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Incremental);
                _controller.Runtime.Commands.Motion.MoveIncremental(axisname, pos, speed);
                // _controller.Runtime.Commands.Motion.WaitForMotionDone(axisname);
                WaitMotionDone(axisname);
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        /// <summary>
        /// 把本地路径脚本加载至控制器内存中
        /// </summary>
        /// <param name="path"></param>
        private void uploadFileToController(string path)
        {
            try
            {
                // First we must read the contents of the file into memory.
                // The .NET API supports uploading file contents as text or as bytes.
                // For this example we will assume the file is a text file.
                string fileContents = File.ReadAllText(path);

                // We will give the file on the controller file system the same
                // name as the file we are uploading from the local file system.
                string fileName = Path.GetFileName(path);

                // The Files API provides access to the controller file system. We can use it to read
                // or write files and even respond to changes in files using the Changed event.
                //
                // To upload the file all we need to provide is the file name and its contents.
                _controller.Files.WriteText(fileName, fileContents);
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        /// <summary>
        /// 初始化后第一次移动至上料端升PIN，后续的脚本运动会自动走到位
        /// 每次在搬运前都可以调用，如果Stage已经到位则不运行，保证搬运逻辑
        /// </summary>
        /// <returns></returns>
        public bool MoveToLoadPos()
        {
            string error;
            DateTime MoveToLoadPosB = DateTime.Now;
            bool hasLock = false;
            try
            {
                DateTime MoveToLoadPosJudegB = DateTime.Now;
                if (!CheckInitalPrepareState())
                {
                    return false;
                }
                //互锁
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    if (!IsEFEMInterLockOutEnable())
                    {
                        //if (IsOnLoadPos())
                        //    SetEFEMInterLockIn(true);
                        throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                    }
                    if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPinWithSize)
                    {
                        CheckIfChangePinSizePos();
                    }
                    SetEFEMInterLockIn(false);
                    //开门
                    OpenInspectDoor(false);
                    //判断是否在装载位置
                    double[] aXYZPosition = new double[3] { 0, 0, 0 };
                    StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);

                    aXYZPosition[0] = result.Axis[AxisStatusItem.PositionFeedback, "X"].Value;
                    aXYZPosition[1] = result.Axis[AxisStatusItem.PositionFeedback, "Z"].Value;
                    aXYZPosition[2] = result.Axis[AxisStatusItem.PositionFeedback, "Theta"].Value;
                    switch (_WaferUpDownMode) 
                    {
                        case WaferUpDownMode.UpDownPinInChhuck:
                        case WaferUpDownMode.UpDownPinOutChuck:
                            {
                                //判断不在上下料位置则需要防呆处理
                                if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) > 0.5)
                                {
                                    if (IsPinUp())
                                    {
                                        if (!DownPin())
                                            return false;
                                    }
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("Z", _stageRunPara._ZLoadPos, 50);
                                }
                                if (Math.Abs(aXYZPosition[0] - _stageRunPara._XLoadPos) > 0.5)
                                {
                                    if (IsPinUp())
                                    {
                                        if (!DownPin())
                                            return false;
                                    }
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("X", _stageRunPara._XLoadPos, 160);
                                }
                                if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 0.5)
                                {
                                    if (IsPinUp())
                                    {
                                        if (!DownPin())
                                            return false;
                                    }
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 360)
                                        homeAxis("Theta");
                                    MoveAxis("Theta", _stageRunPara._TLoadPos, 600);
                                }
                                Debug.WriteLine("---MoveToLoadPosJudge:" + (DateTime.Now - MoveToLoadPosJudegB).TotalMilliseconds);
                                DateTime releaseB = DateTime.Now;
                                if (!Release())
                                    return false;
                                Debug.WriteLine("---releaseTime:" + (DateTime.Now - releaseB).TotalMilliseconds);
                                //if (!UpPin())
                                //    return false;
                                DateTime upS = DateTime.Now;
                                if (!UpPinFast())
                                    return false;
                                Debug.WriteLine("---releaseTime:" + (DateTime.Now - upS).TotalMilliseconds);
                                OpenInspectDoor(true);
                                SetEFEMInterLockIn(true);
                                return true;
                            }
                            break;
                        case WaferUpDownMode.UpDownChuckFixPin:
                        case WaferUpDownMode.UpDownChuckFixPinNoAvoid:
                        {
                                //判断不在上下料位置则需要防呆处理
                                //if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) > 0.5)
                                //{
                                //    if (IsPinUp())
                                //    {
                                //        if (!DownPin())
                                //            return false;
                                //    }
                                //    if (IsWaferExist())
                                //    {
                                //        if (!Fix())
                                //            return false;
                                //    }
                                //    MoveAxis("Z", _stageRunPara._ZLoadPos, 50);
                                //}
                                if (Math.Abs(aXYZPosition[0] - _stageRunPara._XLoadPos) > 0.5)
                                {
                                    //if (IsPinUp())
                                    //{
                                    //    if (!DownPin())
                                    //        return false;
                                    //}
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("X", _stageRunPara._XLoadPos, 160);
                                }
                                if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 0.5)
                                {
                                    //if (IsPinUp())
                                    //{
                                    //    if (!DownPin())
                                    //        return false;
                                    //}
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 360)
                                        homeAxis("Theta");
                                    MoveAxis("Theta", _stageRunPara._TLoadPos, 600);
                                }
                                Debug.WriteLine("---MoveToLoadPosJudge:" + (DateTime.Now - MoveToLoadPosJudegB).TotalMilliseconds);
                                DateTime releaseB = DateTime.Now;
                                //if (!Release())
                                //    return false;
                                Debug.WriteLine("---releaseTime:" + (DateTime.Now - releaseB).TotalMilliseconds);
                                //if (!UpPin())
                                //    return false;
                                DateTime upS = DateTime.Now;
                                //if (!UpPinFast())
                                //    return false;
                                if (!DownChuck())
                                    return false;
                                Debug.WriteLine("---releaseTime:" + (DateTime.Now - upS).TotalMilliseconds);
                                OpenInspectDoor(true);
                                SetEFEMInterLockIn(true);
                                return true;
                            }
                            break;
                        case WaferUpDownMode.UpDownFixPinAndChuck:
                        case WaferUpDownMode.UpDownChuckFixPinWithSize:
                        {
                                //判断不在上下料位置则需要防呆处理
                                if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) > 0.5)
                                {
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("Z", _stageRunPara._ZLoadPos, 50);
                                }
                                if (Math.Abs(aXYZPosition[0] - _stageRunPara._XLoadPos) > 0.5)
                                {
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("X", _stageRunPara._XLoadPos, 160);
                                }
                                if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 0.5)
                                {
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 360)
                                        homeAxis("Theta");
                                    MoveAxis("Theta", _stageRunPara._TLoadPos, 600);
                                }
                                Debug.WriteLine("---MoveToLoadPosJudge:" + (DateTime.Now - MoveToLoadPosJudegB).TotalMilliseconds);
                                DateTime releaseB = DateTime.Now;
                                if (!Release())
                                    return false;
                                Debug.WriteLine("---releaseTime:" + (DateTime.Now - releaseB).TotalMilliseconds);
                                //if (!UpPin())
                                //    return false;
                                DateTime upS = DateTime.Now;
                                //if (!UpPinFast())
                                //    return false;
                                Debug.WriteLine("---releaseTime:" + (DateTime.Now - upS).TotalMilliseconds);
                                OpenInspectDoor(true);
                                SetEFEMInterLockIn(true);
                                return true;
                            }
                            break;
                        default:
                            {
                                error = "The lifting method for the wafer has not been configured";
                                RecordLog(error);
                                throw new Exception(error);
                            }
                            break;
                    }
                   
                }
                else 
                {
                    error = "WaitStageMoveToLoadPosTimeOut";
                    RecordLog(error);
                    throw new Exception();
                }
            }
            catch (Exception ex) { throw ex; }
            finally
            {
                if (hasLock) Monitor.Exit(_mux);
                Debug.WriteLine("---MoveToLoadPosAllTime:" + (DateTime.Now - MoveToLoadPosB).TotalMilliseconds);
            }
            //判断PIN是否升起，升起则降PIN
            /*  if (IsPinUp())
              {
                  if (DownPin())
                  {
                      if (MoveToXZT(_stageRunPara._XLoadPos, _stageRunPara._ZLoadPos, _stageRunPara._TLoadPos))
                      {
                          if (UpPin())
                              return true;
                          else
                              return false;

                      }
                      else
                          return false;
                  }
                  else
                      return false;
              }
              else
              {
                  if (MoveToXZT(_stageRunPara._XLoadPos, _stageRunPara._ZLoadPos, _stageRunPara._TLoadPos))
                  {
                       if (UpPin())
                              return true;
                          else
                              return false;
                  }
                  else
                      return false;
              }*/
            //移动至上料点位
        }
        /// <summary>
        /// 获取脚本运行后的状态 0为正常，其它为错误
        /// </summary>
        /// <returns></returns>
        private int getStage()
        {
            try { return (int)GetStageGlobleI((int)GlobalinfoI.gState); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        /// <summary>
        /// 初始化前需要先传送Stage相关配置参数，此为标志位
        /// </summary>
        private bool _loadParaFlag = false;
        private bool _loadRecParaFlag = false;
        private bool _recParaChange = false;
        /// <summary>
        /// 初始化前需要通过此接口传送Stage系统相关参数
        /// para:Json字符串序列 
        /// </summary>
        public bool LoadSysParaToStage(string para)
        {
            ///设置相关参数
            /*  var strjson = new JObject();
              //IP ini
              StageRunPara  tStageRunPara= new StageRunPara();
              tStageRunPara._IP = JObject.Parse(para)["IP"].ToString();
              //目前只写入调用脚本名字即可 ini
              tStageRunPara._SprialScriptPath = JObject.Parse(para)["SprialScriptPath"].ToString();
              //上下料点位 ini
              tStageRunPara._XLoadPos = Convert.ToDouble(JObject.Parse(para)["XLoadPos"].ToString());
              tStageRunPara._ZLoadPos = Convert.ToDouble(JObject.Parse(para)["ZLoadPos"].ToString());
              tStageRunPara._TLoadPos = Convert.ToDouble(JObject.Parse(para)["TLoadPos"].ToString());
             //光学调试的焦距基准位置 ini
              tStageRunPara._ZInspecPos = Convert.ToDouble(JObject.Parse(para)["_ZInspecPos"].ToString());
             //扫描螺距目前F3000用的是2mm F2000用的是4mm 可以不传送参数，根据写入的机台型号内部选择
              tStageRunPara._Fov = Convert.ToDouble(JObject.Parse(para)["Fov"].ToString());
             //光学调试的相机X轴中心  ini
              tStageRunPara._SensorToOriginal = Convert.ToDouble(JObject.Parse(para)["SensorToOriginal"].ToString());
             //扫描半径目前F3000用的是154mm F2000用的是104mm 可以不传送参数，根据写入的机台型号内部选择 
              tStageRunPara._WaferWaferRadius = Convert.ToDouble(JObject.Parse(para)["WaferWaferRadius"].ToString());
              // 使用的基准相机相关参数：暗场 像素分辨率，用到的行频（NUVU相机8BIn用的最大频率65k) ini
              tStageRunPara._PixelSize = Convert.ToDouble(JObject.Parse(para)["PixelSize"].ToString());
              tStageRunPara._Binning = Convert.ToDouble(JObject.Parse(para)["Binning"].ToString());
              tStageRunPara._CameraLR = Convert.ToDouble(JObject.Parse(para)["CameraLR"].ToString());
              tStageRunPara._SpiralWithWaferFlag = Convert.ToInt32(JObject.Parse(para)["CameraLR"].ToString());
              tStageRunPara._CircleNum = Convert.ToInt32(JObject.Parse(para)["CircleNum"].ToString());
             //明场 ini
              tStageRunPara._PixelSize2 = Convert.ToDouble(JObject.Parse(para)["PixelSize2"].ToString());
              tStageRunPara._Binning2 = Convert.ToDouble(JObject.Parse(para)["Binning2"].ToString());
              tStageRunPara._CameraLR2 = Convert.ToDouble(JObject.Parse(para)["CameraLR2"].ToString());
              tStageRunPara._SpiralWithWaferFlag2 = Convert.ToInt32(JObject.Parse(para)["CameraLR2"].ToString());
              tStageRunPara._CircleNum2 = Convert.ToInt32(JObject.Parse(para)["CircleNum2"].ToString());
              //F3000还有两个暗场通道，预期是参数都是一样的，目前先空着，后续根据情况添加
              //AF 是否启用标志: 1为启用 0为不启用 ini
              tStageRunPara._AFControlFlag = Convert.ToInt32(JObject.Parse(para)["AFControlFlag"].ToString());
              //AF 校准斜率 ini
              tStageRunPara._AFLinearFunSlope = Convert.ToDouble(JObject.Parse(para)["AFLinearFunSlope"].ToString());
              //AF 校准截距 ini
              tStageRunPara._AFLinearFunIntercept = Convert.ToDouble(JObject.Parse(para)["AFLinearFunIntercept"].ToString());
              //AF 校准反馈轴 默认的是"Z" ini
              tStageRunPara._AFVaxisName = JObject.Parse(para)["AFVaxisName"].ToString();
              //AF 和光源矫正用的点位，也可以默认设置一个中心点位，这样点位参数可以不用传送，后续如果要传入可以再添加 ini
              tStageRunPara._AFCalibrationTpostion = Convert.ToDouble(JObject.Parse(para)["AFCalibrationTpostion"].ToString());
              tStageRunPara._AFCalibrationXpostion = Convert.ToDouble(JObject.Parse(para)["AFCalibrationXpostion"].ToString());
              tStageRunPara._AFCalibrationZpostion = Convert.ToDouble(JObject.Parse(para)["AFCalibrationZpostion"].ToString());
              ///AF电压基准  ini
              tStageRunPara._AFVBase = Convert.ToDouble(JObject.Parse(para)["AFVBase"].ToString());
              ///AF电压偏移
              tStageRunPara._AFVOffset = Convert.ToDouble(JObject.Parse(para)["AFVOffset"].ToString());
              ///晶圆尺寸 6 8 12
              tStageRunPara._WaferSize = Convert.ToInt32(JObject.Parse(para)["WaferSize"].ToString());
              ///扫描等级
              tStageRunPara._ScanGrade = Convert.ToInt32(JObject.Parse(para)["ScanGrade"].ToString());
              ///机械类型 F2000 = 1 F3000 = 2
              tStageRunPara._MachineType = Convert.ToInt32(JObject.Parse(para)["MachineType"].ToString());

              StageIOPara tStageIOPara = new StageIOPara();
              //IO的配置都要在 INI 文件里
              tStageIOPara._XairPressure = Convert.ToInt32(JObject.Parse(para)["XairPressure"].ToString());
              tStageIOPara._VacPressure = Convert.ToInt32(JObject.Parse(para)["VacPressure"].ToString());
              tStageIOPara._WaferExist = Convert.ToInt32(JObject.Parse(para)["WaferExist"].ToString());
              tStageIOPara._AFLightControl = Convert.ToInt32(JObject.Parse(para)["AFLightControl"].ToString());
              tStageIOPara._AFVIO = Convert.ToInt32(JObject.Parse(para)["AFVIO"].ToString());
              tStageIOPara._Fix = Convert.ToInt32(JObject.Parse(para)["Fix"].ToString());
              tStageIOPara._SpiralRunFlag = Convert.ToInt32(JObject.Parse(para)["SpiralRunFlag"].ToString());
              tStageIOPara._PinControl = Convert.ToInt32(JObject.Parse(para)["PinControl"].ToString());
              tStageIOPara._PinDown = Convert.ToInt32(JObject.Parse(para)["PinDown"].ToString());
              tStageIOPara._PinUp = Convert.ToInt32(JObject.Parse(para)["PinUp"].ToString());

              if(!_stageRunPara.Compare(tStageRunPara) || !_stageIOPara.Compare(tStageIOPara))
                  _paraChangeFlag = true;
              else
                  _paraChangeFlag = false;
             _stageRunPara = tStageRunPara;
             _stageIOPara = tStageIOPara;
              */

            try
            {
                var strjson = new JObject();
                //上下料点位 ini
                _stageRunPara._XLoadPos = Convert.ToDouble(JObject.Parse(para)["XLoadPos"].ToString());
                _stageRunPara._ZLoadPos = Convert.ToDouble(JObject.Parse(para)["ZLoadPos"].ToString());
                _stageRunPara._TLoadPos = Convert.ToDouble(JObject.Parse(para)["TLoadPos"].ToString());
                //光学调试的焦距基准位置 ini
                _stageRunPara._ZInspecPos = Convert.ToDouble(JObject.Parse(para)["ZInspecPos"].ToString());
                //光学调试的相机X轴中心  ini
                _stageRunPara._SensorToOriginal = Convert.ToDouble(JObject.Parse(para)["SensorToOriginal"].ToString());

                ///AF电压基准  ini
                _stageRunPara._AFVBase = Convert.ToDouble(JObject.Parse(para)["AFVBase"].ToString());
                //AFSum判断阈值
                _stageRunPara.AFSumThreshold = Convert.ToDouble(JObject.Parse(para)["AFSumThreshold"].ToString());
                //AF 校准斜率
                _stageRunPara._AFLinearFunSlope = Convert.ToDouble(JObject.Parse(para)["AFLinearFunSlope"].ToString());
                //AF 校准截距 ini
                _stageRunPara._AFLinearFunIntercept = Convert.ToDouble(JObject.Parse(para)["AFLinearFunIntercept"].ToString());
                _stageRunPara._AFVOffset = Convert.ToDouble(JObject.Parse(para)["AFVOffset"].ToString());
                //AF 是否启用标志: 1为启用 0为不启用 ini
                _stageRunPara._AFControlFlag = Convert.ToInt32(JObject.Parse(para)["AFControlFlag"].ToString());

                //升Chuck 停靠点位 两段速度
                _stageRunPara._ZUpToPinPos = Convert.ToDouble(JObject.Parse(para)["ZUpToPinPos"].ToString());
                _stageRunPara._ZUpToPinVel1 = Convert.ToDouble(JObject.Parse(para)["ZUpToPinVel1"].ToString());
                _stageRunPara._ZUpToPinVel2 = Convert.ToDouble(JObject.Parse(para)["ZUpToPinVel2"].ToString());
                //降Chuck 停靠点位 两段速度
                _stageRunPara._ZDownToPinPos = Convert.ToDouble(JObject.Parse(para)["ZDownToPinPos"].ToString());
                _stageRunPara._ZDownToPinVel1 = Convert.ToDouble(JObject.Parse(para)["ZDownToPinVel1"].ToString());
                _stageRunPara._ZDownToPinVel2 = Convert.ToDouble(JObject.Parse(para)["ZDownToPinVel2"].ToString());
                // _WaferUpDownMode = ()Convert.ToInt32(JObject.Parse(para)["TransferWaferMode"].ToString());
                int liftmethod = Convert.ToInt32(JObject.Parse(para)["WaferliftingMethod"].ToString());
                if (Enum.IsDefined(typeof(WaferUpDownMode), liftmethod))
                {
                    _WaferUpDownMode = (WaferUpDownMode)liftmethod;
                    // 使用 myColor 进行操作
                }
                else
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                    {
                        error = $"The WaferliftingMethod parameter:{liftmethod} from Recipe is not supported ";
                    }
                    else
                    {
                        error = $"Stage不支持配方中的晶圆升降方式参数：{liftmethod}";
                    }
                    RecordLog(error);
                    throw new Exception(error);
                }
                
                //Z轴预聚焦补偿mm
                double tAFCompensation = Convert.ToDouble(JObject.Parse(para)["ZPreAFCompensation"].ToString());
                if (tAFCompensation < -2 || tAFCompensation > 2)
                {
                    _loadParaFlag = false;
                    throw new Exception($"SetStageRunParaZPreAFCompensationFault:{tAFCompensation}");
                }
                _stageRunPara._AFCompensation = tAFCompensation;
            }
            catch (Exception ex)
            {
                _loadParaFlag = false;
                throw ex;
            }
            ///标志位置位
            _loadParaFlag = true;
            return true;
        }
        /// <summary>
        /// 加载配方参数，运行扫描前需要加载；
        /// </summary>
        /// <param name="para"></param>
        public bool LoadRecipeParaToStage(string para)
        {
            var strjson = new JObject();
            try
            {
                ///晶圆尺寸 6 8 12
                int tWaferSize = Convert.ToInt32(JObject.Parse(para)["WaferSize"].ToString());
                if (tWaferSize != 8 && tWaferSize != 12 && tWaferSize != 6)
                {
                    _recParaChange = false;
                    _loadRecParaFlag = false;
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Do Not Support Recipe WaferSize:{tWaferSize}");
                    else
                        throw new Exception("不支持配方晶圆尺寸:{tWaferSize}");
                }
                if (_stageRunPara._WaferSize != tWaferSize)
                {
                    _recParaChange = true;
                    _stageRunPara._WaferSize = tWaferSize;
                }
                if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPinWithSize) 
                {
                    CompareWaferSizePosWithRecipe();
                }
                ///扫描等级
                int tScanGrade = Convert.ToInt32(JObject.Parse(para)["ScanGrade"].ToString());
                if (tScanGrade < 0)
                {
                    _recParaChange = false;
                    _loadRecParaFlag = false;
                    if(_languageMode == LanguageMode.EN)
                        throw new Exception("Set Stage RunPara ScanGrade Fault:{tScanGrade}");
                    else
                        throw new Exception("设置Stage运行参数扫描等级故障:{tScanGrade}");
                }
                if (_stageRunPara._ScanGrade != tScanGrade)
                {
                    _recParaChange = true;
                    _stageRunPara._ScanGrade = tScanGrade;
                }
                if (_stageRunPara._WaferSize == 8)
                {
                    _stageRunPara._WaferWaferRadius = _ScanRadius[1];
                    //_stageRunPara._Fov = _Fovs[1];
                }
                else if (_stageRunPara._WaferSize == 12)
                {
                    _stageRunPara._WaferWaferRadius = _ScanRadius[2];
                    //_stageRunPara._Fov = _Fovs[2];
                }
                else if (_stageRunPara._WaferSize == 6)
                {
                    _stageRunPara._WaferWaferRadius = _ScanRadius[0];
                }
                ////像素尺寸：mm
                //_stageRunPara._PixelSize = Convert.ToDouble(JObject.Parse(para)["PixelSize"].ToString());
                ////相机传感器宽度：像素
                //_stageRunPara._PixelCount = Convert.ToDouble(JObject.Parse(para)["PixelCount"].ToString());
                ////Bin
                //_stageRunPara._Binning = Convert.ToDouble(JObject.Parse(para)["Binning"].ToString());
                ////相机触发频率
                //_stageRunPara._CameraLR = Convert.ToDouble(JObject.Parse(para)["CameraLR"].ToString());
                ////螺距
                //_stageRunPara._Fov = Convert.ToDouble(JObject.Parse(para)["Fov"].ToString());

                //像素尺寸：mm
                double tPixelSize = Convert.ToDouble(JObject.Parse(para)["PixelSize"].ToString());
                //相机传感器宽度：像素
                double tPixelCount = Convert.ToDouble(JObject.Parse(para)["PixelCount"].ToString());
                //Bin
                double tBinning = Convert.ToDouble(JObject.Parse(para)["Binning"].ToString());
                //相机触发频率
                double tCameraLR = Convert.ToDouble(JObject.Parse(para)["CameraLR"].ToString());
                //螺距
                double tFov = Convert.ToDouble(JObject.Parse(para)["Fov"].ToString());
                //半径
                //double tWaferWaferRadius = Convert.ToDouble(JObject.Parse(para)["WaferRadius"].ToString());
                //同心圆圈数
                int tCircleNum = Convert.ToInt32(JObject.Parse(para)["CircleNum"].ToString());
                //T轴扫描触发起始角度
                double tTTriggerStartAngle = Convert.ToDouble(JObject.Parse(para)["TTriggerStartAngle"].ToString()) % 360;
               
                if (tPixelSize < 0.0000001 || tPixelSize > 0.1) 
                {
                    _loadRecParaFlag = false;
                    if(_languageMode == LanguageMode.EN)
                        throw new Exception("Set Stage RunPara PixelSize Fault:{tPixelSize}");
                    else
                        throw new Exception("设置Stage运行参数像素尺寸故障:{tPixelSize}");
                }
                if (tPixelCount < 1.0 || tPixelCount > 100000)
                {
                    _loadRecParaFlag = false;
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception($"Set Stage RunPara PixelCoun Fault:{tPixelCount}");
                    else
                        throw new Exception($"设置Stage运行参数像素个数故障:{tPixelCount}");
                }
                if (tBinning < 0.999 || tBinning > 8.001)
                {
                    _loadRecParaFlag = false;
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception($"Set Stage RunPara Bin Fault:{tBinning}");
                    else
                        throw new Exception($"设置Stage运行参数Bin故障:{tBinning}");
                }
                if (tCameraLR < 1.0 || tCameraLR > 2000000)
                {
                    _loadRecParaFlag = false;
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception($"Set Stage RunPara CameraLR Fault:{tCameraLR}");
                    else
                        throw new Exception($"设置Stage运行参数相机行频故障:{tCameraLR}");
                }
                if (tFov < 0.1 || tFov > 10)
                {
                    _loadRecParaFlag = false;
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception($"Set Stage RunPara Fov Fault:{tFov}");
                    else
                        throw new Exception($"设置Stage运行参数螺距故障:{tFov}");
                }
                if (tCircleNum < 1 || tCircleNum > (_stageRunPara._WaferWaferRadius / tFov))
                {
                    _loadRecParaFlag = false;
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception($"Set Stage RunPara CircleNum Fault:{tCircleNum}");
                    else
                        throw new Exception($"设置Stage运行参数圈数故障:{tCircleNum}");
                }
                // if(tWaferWaferRadius < 1.0 || tWaferWaferRadius > 160)
                // {
                //     _loadRecParaFlag = false;
                //     throw new Exception("SetWaferRadiusParaError");
                // }
                if (_stageRunPara._PixelSize != tPixelSize) { _recParaChange = true; }
                if (_stageRunPara._PixelCount != tPixelCount) { _recParaChange = true; }
                if (_stageRunPara._Binning != tBinning) { _recParaChange = true; }
                if (_stageRunPara._CameraLR != tCameraLR) { _recParaChange = true; }
                if (_stageRunPara._Fov != tFov) { _recParaChange = true; }
                if (_stageRunPara._CircleNum != tCircleNum) { _recParaChange = true; }
                if (_stageRunPara._TTriggerStartAngle != tTTriggerStartAngle) { _recParaChange = true; }

                //if (_stageRunPara._WaferWaferRadius != tWaferWaferRadius) { _recParaChange = true; }
                //像素尺寸：mm
                _stageRunPara._PixelSize = tPixelSize;
                //相机传感器宽度：像素
                _stageRunPara._PixelCount = tPixelCount;
                //Bin
                _stageRunPara._Binning = tBinning;
                //相机触发频率
                _stageRunPara._CameraLR = tCameraLR;
                //螺距
                _stageRunPara._Fov = tFov;
                //同心圆圈数
                _stageRunPara._CircleNum = tCircleNum;
                //T轴强制停止位置默认是0忽略强制
                //_stageRunPara._StopTPos = Convert.ToDouble(JObject.Parse(para)["StopTpos"].ToString());
                //T轴触发起始角度
                _stageRunPara._TTriggerStartAngle = tTTriggerStartAngle;
                //大颗粒时间数据
                JArray data = JArray.Parse(JObject.Parse(para)["Data"].ToString());
                List<Tuple<int, int>> BigParticles = new List<Tuple<int, int>>();
                foreach (JArray item in data)
                {
                    if (item.Count == 2 && item[0].Type == JTokenType.Integer && item[1].Type == JTokenType.Integer)
                    {
                        BigParticles.Add(new Tuple<int, int>((int)item[0], (int)item[1]));
                    }
                    else
                    {
                        throw new InvalidOperationException("JArray 包含的元素格式不正确，无法转换为 Tuple<int, int>。");
                    }
                }
                if(BigParticles.Count > 100) 
                {
                    throw new InvalidOperationException("大颗粒数据量超过100");
                }
                else 
                {
                    long ParticleNum = GetStageGlobleI(200);
                    for (int i = 0; i < ParticleNum; i++)
                    {
                        SetStageGlobleI(211 + 2 * i, 0);
                        SetStageGlobleI(211 + 2 * i + 1, 0);
                    }

                    SetStageGlobleI(200, BigParticles.Count);
                    for (int i = 0; i < BigParticles.Count; i++)
                    {
                        SetStageGlobleI(211 + 2*i, BigParticles[i].Item1);
                        SetStageGlobleI(211 + 2 * i + 1, BigParticles[i].Item2);
                    }
                }

                // 是否启用APPDataSave
                _stageRunPara._APPDataSaveFlag = Convert.ToInt32(JObject.Parse(para)["DataSave"].ToString());
                //APPData路径
                if (_stageRunPara._APPDataSaveFlag == 1)//绝对路径包含文件名字
                {
                    string path = JObject.Parse(para)["DataSavePath"].ToString();
                    if (!Path.IsPathRooted(path))
                    {
                        _stageRunPara._APPDataSavePath = null;
                        if (_languageMode == LanguageMode.EN)
                            throw new Exception($"Set DataSavePath Fault:{path}");
                        else
                            throw new Exception($"设置Stage数据保存路径故障:{path}");
                    }
                    else { _stageRunPara._APPDataSavePath = path; }
                }
                _stageRunPara._ScanCountForAppData = Convert.ToInt32(JObject.Parse(para)["SaveForScanCount"].ToString());
            }
            catch (Exception ex) 
            {
                _loadRecParaFlag = false;
                throw ex;
            }
            _loadRecParaFlag = true;
            return true;
        }
        /// <summary>
        /// 获取AF接入Stage后反馈的电压
        /// </summary>
        /// <returns></returns>
        const int AFNUM = 3;
        public bool GetAutoFocusPSDValue(out double value)
        {

            try
            {
                value = double.NaN;

                if (!CheckInitalPrepareState())
                {
                    return false;
                }
                if (!HasWaferFix())
                {
                    return false;
                }
                SetIO("Z", _stageIOPara._AFLightControl, true);
                //Thread.Sleep(200);
                //取平均值
                double afv = 0.0;
                for (int i = 0; i < AFNUM; i++)
                {
                    afv += _controller.Runtime.Commands.IO.AnalogInputGet(_stageRunPara._AFVaxisName, _stageIOPara._AFVIO);
                    Thread.Sleep(5);
                }
                value = afv / AFNUM;
                //SetIO("Z", _stageIOPara._AFLightControl, false);
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public double GetAFSumValue()
        {
            try
            {
                double afvSum = 0.0;
                for (int i = 0; i < AFNUM; i++)
                {
                    afvSum += _controller.Runtime.Commands.IO.AnalogInputGet(_stageRunPara._AFVSumaxisName, _stageIOPara._AFSumVIO);
                    Thread.Sleep(5);
                }
                return afvSum / AFNUM;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        const double VMAX = 100;
        const double POSLIMIT = 18.0;
        /// <summary>
        /// 系统调用获取AF 位置电压曲线数据
        /// </summary>
        /// <param name="velocity"></param>
        /// <param name="step"></param>
        /// <param name="startPos"></param>
        /// <param name="endPos"></param>
        /// <param name="data"></param>
        /// <returns></returns>
        public bool GetAutoFocusCalibrationData(double velocity, double step, double startPos, double endPos, out List<double[]> data)
        {
            data = new List<double[]>();
            #region prepareCheck
            if (!CheckInitalPrepareState())
            {
                return false;
            }
            if (!IsEFEMInterLockOutEnable())
            {
                //if (IsOnLoadPos())
                //    SetEFEMInterLockIn(true);
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                if (_languageMode == LanguageMode.EN)
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                else
                    throw new Exception(StageErrorInfoZ.触发EFEM互锁.ToString());
            }
            SetEFEMInterLockIn(false);
            //关门
            CloseInspectDoor(false);
            if (velocity > VMAX)
            {
                string err;
                if(_languageMode == LanguageMode.EN)
                    err = $"Z Axis Velocity:{velocity} out of range:{VMAX}";
                else
                    err = $"Z轴速度:{velocity} 超出上限:{VMAX}";
                RecordLog(err);
                throw new Exception(err);
            }
            if (step > Math.Abs(endPos - startPos))
            {
                string err;
                if(_languageMode == LanguageMode.EN)
                    err = $"Z MoveStep:{step} > MoveRange:{endPos - startPos}";
                else
                    err = $"Z 移动步距:{step} > 移动范围:{endPos - startPos}";
                RecordLog(err);
                throw new Exception(err);
            }
            if (Math.Abs(startPos) > POSLIMIT || Math.Abs(endPos) > POSLIMIT)
            {
                string err;
                if (_languageMode == LanguageMode.EN)
                    err = $"StartPos:{startPos} EndPos:{endPos} out of range:{POSLIMIT}";
                else
                    err = $"开始位置:{startPos} 结束位置:{endPos} 超出限位:{POSLIMIT}";
                RecordLog(err);
                throw new Exception(err);
            }
            if (!HasWaferFix())
            {
                return false;
            }
            #endregion
            try
            {
                //移动至校准点位
                //double xPos = 0;
                //if (_stageRunPara._SensorToOriginal > 0)
                //    xPos = _stageRunPara._SensorToOriginal - _stageRunPara._WaferWaferRadius;
                //else
                //    xPos = _stageRunPara._SensorToOriginal + _stageRunPara._WaferWaferRadius;
                double xPos = 0;
                if (_stageRunPara._SensorToOriginal > 0)
                    xPos = _stageRunPara._SensorToOriginal - _stageRunPara._WaferWaferRadius + 6 * _stageRunPara._Fov;
                else
                    xPos = _stageRunPara._SensorToOriginal + _stageRunPara._WaferWaferRadius - 6 * _stageRunPara._Fov;

                MoveAxis("X", xPos, 20);
                MoveAxis("Theta", _stageRunPara._TLoadPos, 20);
                MoveAxis("Z", startPos, 20);

                if (startPos < endPos)
                {

                    double[] pais = new double[2];
                    double value;
                    pais[0] = startPos;
                    GetAutoFocusPSDValue(out value);
                    pais[1] = value;
                    data.Add(pais);
                    startPos = startPos + Math.Abs(step);
                    while (startPos < endPos)
                    {
                        MoveAxis("Z", startPos, velocity);
                        double[] values = new double[2];
                        values[0] = startPos;
                        double val;
                        GetAutoFocusPSDValue(out val);
                        values[1] = val;
                        data.Add(values);
                        startPos = startPos + Math.Abs(step);
                    }
                }
                else
                {
                    double[] pais = new double[2];
                    pais[0] = startPos;
                    double value;
                    GetAutoFocusPSDValue(out value);
                    pais[1] = value;
                    data.Add(pais);
                    startPos = startPos - Math.Abs(step);
                    while (startPos > endPos)
                    {
                        MoveAxis("Z", startPos, velocity);
                        double[] values = new double[2];
                        values[0] = startPos;
                        double val;
                        GetAutoFocusPSDValue(out val);
                        values[1] = val;
                        data.Add(values);
                        startPos = startPos - Math.Abs(step);
                    }
                }
            }
            catch (Exception ex)
            {
                RecordLog(ex.Message);
                throw new Exception(ex.Message);
            }
            return true;
        }
        /// <summary>
        /// 上料后衔接的物料固定流程
        /// </summary>
        /// <returns></returns>
        private bool HasWaferFix()
        {
            if (!IsWaferExist())
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ScanWithoutWafer]);//return false;
                else
                    throw new Exception(StageErrorInfoZ.扫描检测无晶圆.ToString());
            }
                
            //预先打开给降PIN一些时间
            //SetIO("Z", _stageIOPara._Fix, true);
            SetIO("Z", _stageIOPara._Fix, false);
            if (_WaferUpDownMode == WaferUpDownMode.UpDownPinInChhuck
                || _WaferUpDownMode == WaferUpDownMode.UpDownPinOutChuck)
            {
                if (!DownPin())
                {
                    return false;
                }
            }
            if (!Fix())
            {
                return false;
            }
            return true;
        }
        /// <summary>
        /// 查询Wafer吸附真空压力是否达到设定阈值
        /// </summary>
        /// <returns></returns>
        public bool IsWaferFix() 
        {
            return GetIO("Z", _stageIOPara._VacPressure);
        }
        const double ZOFFSETMAX = 0.5;//mm
            /// <summary>
            /// 聚焦距离校准
            /// </summary>
            /// <returns></returns> 
        public bool MoveToCalPosOld(int num = 0)
        {
            DateTime MtcS = DateTime.Now; 
            double xPos = 0;
            bool hasLock = false;
            try
            {
                DateTime CFS = DateTime.Now;
                if (!CheckInitalPrepareState())
                {
                    return false;
                }
                if (!IsEFEMInterLockOutEnable())
                {
                    //if (IsOnLoadPos())
                    //    SetEFEMInterLockIn(true);
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception(StageErrorInfoE.TriggerEFEMInterLock.ToString());
                    else
                        throw new Exception(StageErrorInfoZ.触发EFEM互锁.ToString());
                }
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    SetEFEMInterLockIn(false);
                    //关门
                    CloseInspectDoor(false);

                    if (!HasWaferFix())
                    {
                        return false;
                    }
                    Debug.WriteLine("---CloseFixTime:" + (DateTime.Now - CFS).TotalMilliseconds);
                    xPos = _stageRunPara._SensorToOriginal;
                    DateTime MoveToCalPosS = DateTime.Now;
                    if (num < 1)
                    {
                        if (_stageRunPara._SensorToOriginal > 0)
                            xPos = _stageRunPara._SensorToOriginal - _stageRunPara._WaferWaferRadius + 6 * _stageRunPara._Fov;
                        else
                            xPos = _stageRunPara._SensorToOriginal + _stageRunPara._WaferWaferRadius - 6 * _stageRunPara._Fov;
                    }

                    //MoveAxis("X", _stageRunPara._AFCalibrationXpostion, 50);
                    //MoveAxis("X", _stageRunPara._SensorToOriginal, 50);
                    //MoveAxis("X", xPos, 160, false);
                   // MoveAxis("Theta", _stageRunPara._TLoadPos, 600, false);
                    //MoveAxis("Z", _stageRunPara._ZInspecPos, 50, false);

                   // MoveAxis("X", xPos, 160, true);
                    //MoveAxis("Theta", _stageRunPara._TLoadPos, 600, true);
                    //MoveAxis("Z", _stageRunPara._ZInspecPos, 50, true);

                    _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                    _controller.Runtime.Commands.Motion.MoveAbsolute(
                        new string[] { "X", "Theta", "Z" }, 
                        new double[] { xPos, _stageRunPara._TLoadPos, _stageRunPara._ZInspecPos }, 
                        new double[] {180, 600, 60});
                    //_controller.Runtime.Commands.Motion.WaitForMotionDone(new string[] { "X", "Theta", "Z" });
                    WaitMotionDone(new string[] { "X", "Theta", "Z" });

                    Debug.WriteLine("---MoveToCalPosTime:" + (DateTime.Now - MoveToCalPosS).TotalMilliseconds);
                    if (num > 0)//用于暗场PSD
                        return true;
                    DateTime GetAFS = DateTime.Now;
                    // AFV = aZ + b; z = (AFV-b)/a  b还需要加不同材质的偏移
                    double afvCurrent;
                    GetAutoFocusPSDValue(out afvCurrent);
                    Debug.WriteLine("---GetAFTime:" + (DateTime.Now - GetAFS).TotalMilliseconds);
                    if (double.IsNaN(afvCurrent))
                    {
                        if (_languageMode == LanguageMode.EN)
                            throw new Exception("AFGetPSDAbnormalValue PleaseCheckAF");
                        else
                            throw new Exception("自动聚焦获取PSD异常值，需要检查自动聚焦");
                    }
                    DateTime MoveToRealCalS = DateTime.Now;
                    double zCurrentPos;
                    if (Math.Abs(_stageRunPara._AFLinearFunSlope - 0) < 0.000001)
                        zCurrentPos = 0;
                    else
                        zCurrentPos = (afvCurrent - _stageRunPara._AFLinearFunIntercept - _stageRunPara._AFVOffset) / _stageRunPara._AFLinearFunSlope;
                    double zoffset = _stageRunPara._ZInspecPos - zCurrentPos;
                    if (Math.Abs(zoffset) > ZOFFSETMAX)
                    {
                        if (_languageMode == LanguageMode.EN)
                            throw new Exception("AFCalibrationZOffsetValue:" + Math.Abs(zoffset).ToString() + "mm" + "OutOfRange" + " PleaseCheckAFCalibrationPara");
                        else
                            throw new Exception("自动聚焦校准后Z轴偏移值:" + Math.Abs(zoffset).ToString() + "mm" + "超出范围" + "请检查自动聚焦");
                    }
                    double zRealPos = _stageRunPara._ZInspecPos + zoffset;
                    if (Math.Abs(zRealPos) > POSLIMIT)
                    {
                        if (_languageMode == LanguageMode.EN)
                            throw new Exception("AFCalibrationZFocusPos:" + zRealPos.ToString() + "mm" + "OutOfRange" + " PleaseCheckAFCalibrationPara");
                        else
                            throw new Exception("自动聚焦校准后的Z轴位置：" + zRealPos.ToString() + "mm" + "超出范围" + "请检查自动聚焦");
                    }
                    SetStageGlobleR((int)GlobalInfo.gZinspect, zRealPos);
                    _controller.Runtime.Commands.Motion.MoveAbsolute("Z", zRealPos, 60);
                    //_controller.Runtime.Commands.Motion.WaitForMotionDone("Z");
                    WaitMotionDone("Z");
                    //MoveAxis("Z", zRealPos, 50, true);
                    Debug.WriteLine("---GetAFZTime:" + (DateTime.Now - GetAFS).TotalMilliseconds);
                    return true;
                }
                else 
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("WaitStageMoveToCalPosTimeOut");
                    else
                        throw new Exception("等待Stage移动到校准位置超时");
                }
            }
            catch (Exception ex) 
            { 
                if(_languageMode == LanguageMode.EN)
                    throw new Exception(ex.Message +"_" + "XPos:" + xPos.ToString() + "_Original:" + _stageRunPara._SensorToOriginal.ToString() + "_WR:" + _stageRunPara._WaferWaferRadius.ToString() + "_FOV:" + _stageRunPara._Fov.ToString()); 
                else
                    throw new Exception(ex.Message + "_" + "XPos:" + xPos.ToString() + "_Original:" + _stageRunPara._SensorToOriginal.ToString() + "_WR:" + _stageRunPara._WaferWaferRadius.ToString() + "_FOV:" + _stageRunPara._Fov.ToString());
            }
            finally { if(hasLock) Monitor.Exit(_mux); Debug.WriteLine("---MoveToCallAllTime:" + (DateTime.Now - MtcS).TotalMilliseconds); }
           
        }
        public bool MoveToCalPos(int num = 0)
        {
            DateTime MtcS = DateTime.Now;
            double xPos = 0;
            double afvCurrent = 0;
            string error;
            bool hasLock = false;
            try
            {
                DateTime CFS = DateTime.Now;
                if (!CheckInitalPrepareState())
                {
                    return false;
                }
                if (!IsEFEMInterLockOutEnable())
                {
                    //if (IsOnLoadPos())
                    //    SetEFEMInterLockIn(true);
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                    else
                        throw new Exception(StageErrorInfoZ.触发EFEM互锁.ToString());
                }
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    //if (_WaferUpDownMode == WaferUpDownMode.UpDownChuckFixPinWithSize)
                    //{
                    //    CheckIfChangePinSizePos();
                    //}
                    SetEFEMInterLockIn(false);
                    //关门
                    CloseInspectDoor(false);
                    switch (_WaferUpDownMode)
                    {
                        case WaferUpDownMode.UpDownPinInChhuck:
                        case WaferUpDownMode.UpDownPinOutChuck:
                            {
                                if (!HasWaferFix())
                                {
                                    return false;
                                }
                            }
                            break;
                        case WaferUpDownMode.UpDownChuckFixPin:
                            {
                                if (!UpChuck())
                                {
                                    return false;
                                }
                                if (!isPinInAvoidPos())
                                {
                                    ChangePinPosWithInitAvoidance(true, false);
                                }
                            }
                            break;
                        case WaferUpDownMode.UpDownChuckFixPinNoAvoid:
                            {
                                if (!UpChuck())
                                {
                                    return false;
                                }
                            }
                            break;
                        case WaferUpDownMode.UpDownFixPinAndChuck:
                            {

                            }
                            break;
                        default:
                            {

                            }
                            break;
                    }
                    //if (!HasWaferFix())
                    //{
                    //    return false;
                    //}
                   
                    if (_stageRunPara._AFControlFlag == 0) { return true; }

                    Debug.WriteLine("---CloseFixTime:" + (DateTime.Now - CFS).TotalMilliseconds);
                    xPos = _stageRunPara._SensorToOriginal;
                   
                    int FovOffsetNum = 6;//mm 绕过多余的余量
                    DateTime MoveToCalPosS = DateTime.Now;
                    
                    if (num < 1)
                    {
                        if (_stageRunPara._SensorToOriginal > 0)
                            xPos = _stageRunPara._SensorToOriginal - _stageRunPara._WaferWaferRadius + FovOffsetNum;
                        else
                            xPos = _stageRunPara._SensorToOriginal + _stageRunPara._WaferWaferRadius - FovOffsetNum;
                    }
                    //先打开AFlight
                    SetIO("Z", _stageIOPara._AFLightControl, true);

                    _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                    _controller.Runtime.Commands.Motion.MoveAbsolute(
                        new string[] { "X", "Theta", "Z" },
                        new double[] { xPos, _stageRunPara._TLoadPos, _stageRunPara._ZInspecPos },
                        new double[] { 180, 600, 60 });
                    //_controller.Runtime.Commands.Motion.WaitForMotionDone(new string[] { "X", "Theta", "Z" });
                    WaitMotionDone(new string[] { "X", "Theta", "Z" });
                    if (_stageRunPara._AFControlFlag > 0)
                    {
                        //读AFSum基准判断是否在晶圆内部且AF反馈电压正常
                        double AFSum = GetAFSumValue();

                        if (AFSum < _stageRunPara.AFSumThreshold)
                        {
                            //二次往晶圆内部移动一个FOV 再次判断
                            if (_stageRunPara._SensorToOriginal > 0)
                                xPos = xPos + _stageRunPara._Fov;
                            else
                                xPos = xPos - _stageRunPara._Fov;
                            _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                            _controller.Runtime.Commands.Motion.MoveAbsolute(
                                new string[] { "X", "Theta", "Z" },
                                new double[] { xPos, _stageRunPara._TLoadPos, _stageRunPara._ZInspecPos },
                                new double[] { 180, 600, 60 });
                            //_controller.Runtime.Commands.Motion.WaitForMotionDone(new string[] { "X", "Theta", "Z" });
                            WaitMotionDone(new string[] { "X", "Theta", "Z" });
                            AFSum = GetAFSumValue();
                            if (AFSum < _stageRunPara.AFSumThreshold)
                            {
                                //三次往晶圆内部移动一个FOV 再次判断
                                if (_stageRunPara._SensorToOriginal > 0)
                                    xPos = xPos + _stageRunPara._Fov;
                                else
                                    xPos = xPos - _stageRunPara._Fov;
                                _controller.Runtime.Commands.MotionSetup.SetupTaskTargetMode(TargetMode.Absolute);
                                _controller.Runtime.Commands.Motion.MoveAbsolute(
                                    new string[] { "X", "Theta", "Z" },
                                    new double[] { xPos, _stageRunPara._TLoadPos, _stageRunPara._ZInspecPos },
                                    new double[] { 180, 600, 60 });
                                //_controller.Runtime.Commands.Motion.WaitForMotionDone(new string[] { "X", "Theta", "Z" });
                                WaitMotionDone(new string[] { "X", "Theta", "Z" });
                                AFSum = GetAFSumValue();
                                if (AFSum < _stageRunPara.AFSumThreshold)
                                {
                                    GetAutoFocusPSDValue(out afvCurrent);
                                    error = "AFSumV:" + AFSum.ToString() + "V" + " < AFSumVThreshold:" + _stageRunPara.AFSumThreshold.ToString() + "V";
                                    RecordLog(error);
                                    throw new Exception(error);
                                }
                            }
                        }
                        Debug.WriteLine("---MoveToCalPosTime:" + (DateTime.Now - MoveToCalPosS).TotalMilliseconds);
                        if (num > 0)//用于暗场PSD
                            return true;
                        DateTime GetAFS = DateTime.Now;
                        // AFV = aZ + b; z = (AFV-b)/a  b还需要加不同材质的偏移
                        //只用斜率，AFV = aZ =》 AFCurrent-AFBase = a(Zinspect - Zreal)
                        //Zinspect - Zreal = (AFCurrent - AFBase)/a
                        //Zreal = Zinspect - (AFCurrent - AFBase)/a
                        GetAutoFocusPSDValue(out afvCurrent);
                        Debug.WriteLine("---GetAFTime:" + (DateTime.Now - GetAFS).TotalMilliseconds);
                        if (double.IsNaN(afvCurrent))
                        {
                            if(_languageMode == LanguageMode.EN)
                                error = $"AFGetPSDAbnormalValue:{afvCurrent}V";
                            else
                                error = $"自动聚焦获取异常值:{afvCurrent}V";
                            RecordLog(error);
                            throw new Exception(error);
                        }
                        DateTime MoveToRealCalS = DateTime.Now;
                        //double zCurrentPos;
                        if (Math.Abs(_stageRunPara._AFLinearFunSlope - 0) < 0.000001)
                        {
                            //zCurrentPos = 0;
                            if(_languageMode != LanguageMode.EN)
                                error = $"AFLinearFunSlopeFault:{_stageRunPara._AFLinearFunSlope.ToString()}";
                            else
                                error = $"自动聚焦线性斜率故障:{_stageRunPara._AFLinearFunSlope.ToString()}";
                            RecordLog(error);
                            throw new Exception(error);
                        }
                        else
                        {
                            //zCurrentPos = (afvCurrent - _stageRunPara._AFLinearFunIntercept - _stageRunPara._AFVOffset) / _stageRunPara._AFLinearFunSlope;
                            double zoffset = (afvCurrent - _stageRunPara._AFVBase) / _stageRunPara._AFLinearFunSlope;
                            if (Math.Abs(zoffset) > ZOFFSETMAX)
                            {
                                if(_languageMode != LanguageMode.EN)
                                    error = "AFCalibrationZOffsetValue:" + Math.Abs(zoffset).ToString() + "mm" + "OutOfRange" + " PleaseCheckAFCalibrationPara";
                                else
                                    error = "自动聚焦Z轴偏移量e:" + Math.Abs(zoffset).ToString() + "mm" + "超出范围" + " 请检查自动聚焦";
                                RecordLog(error);
                                throw new Exception(error);
                            }
                            double zRealPos = _stageRunPara._ZInspecPos - zoffset + _stageRunPara._AFCompensation;
                            _AFZOffset = _stageRunPara._AFCompensation;
                            //if (Math.Abs(zRealPos) > POSLIMIT)
                            //{
                            //    throw new Exception("AFCalibrationZFocusPos:" + zRealPos.ToString() + "mm" + "OutOfRange" + " PleaseCheckAFCalibrationPara");
                            //}
                            if(zRealPos < _stageRunPara._ZDownToPinPos) 
                            {
                                string einfo; 
                                if(_languageMode == LanguageMode.EN)
                                    einfo = $"After AF ZPos:{zRealPos} < ZPinPos:{_stageRunPara._ZDownToPinPos}";
                                else
                                    einfo = $"自动聚焦后Z轴位置:{zRealPos} < 放片位置:{_stageRunPara._ZDownToPinPos}";
                                RecordLog(einfo);
                                throw new Exception(einfo);
                            }
                            SetStageGlobleR((int)GlobalInfo.gZinspect, zRealPos);
                            _controller.Runtime.Commands.Motion.MoveAbsolute("Z", zRealPos, 60);
                            //_controller.Runtime.Commands.Motion.WaitForMotionDone("Z");
                            WaitMotionDone("Z");
                            //MoveAxis("Z", zRealPos, 50, true);
                            Debug.WriteLine("---GetAFZTime:" + (DateTime.Now - GetAFS).TotalMilliseconds);
                        }
                    }
                    return true;
                }
                else 
                {
                    if (_languageMode == LanguageMode.EN)
                        error = "WaitStageMoveToCalPosTimeOut";
                    else
                        error = "等待Stage移动到校准位置超时";
                    RecordLog(error);
                    throw new Exception(error); 
                }
                  
            }
            catch (Exception ex)
            {
                error = ex.Message + "_AF:" + afvCurrent.ToString() + "_" + "XPos:" + xPos.ToString();
                RecordLog(error);
                throw new Exception(error);
            }
            finally { if(hasLock) Monitor.Exit(_mux); Debug.WriteLine("---MoveToCallAllTime:" + (DateTime.Now - MtcS).TotalMilliseconds); }

        }
        /// <summary>
        /// 执行动作之前的准备判断
        /// </summary>
        /// <returns></returns>
        private bool CheckInitalPrepareState()
        {
            if (_controller == null)
            {
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageControllerIsNull]);
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageControllerIsNull]);//return false;
            }
            if (!_loadParaFlag)
            {
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.SystemParaNotSet]);
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.SystemParaNotSet]);
            }
            if (!_initialFlag)
            {
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageNotInitialize]);
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageNotInitialize]);
            }
            if (!IsAirPressureReady()) 
            {
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.AirFault]);
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.AirFault]);
            }
            if(_runFlag) 
            {
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageIsScanning]);
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageIsScanning]); 
            }
            return true;
        }
        /// <summary>
        /// 单步操作准备判断
        /// </summary>
        /// <returns></returns>
        private bool CheckInitalPrepareStateSingle()
        {
            if (_controller == null)
            {
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageControllerIsNull]);
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageControllerIsNull]);//return false;
            }
            if (!_initialFlag)
            {
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageNotInitialize]);
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.StageNotInitialize]);
            }
            if (!IsAirPressureReady())
            {
                RecordLog(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.AirFault]);
                throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.AirFault]);
            }
            return true;
        }
        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private bool ResetState()
        {
            //设重置运动停止状态
            //关闭AF功能
            try
            {
                _controller.Runtime.Commands.Execute("AutofocusOff(Z)");
                SetIO("Z", _stageIOPara._SpiralRunFlag, false);
                SetIO("Z", _stageIOPara._AFLightControl, false);
                SetStageGlobleI((int)GlobalinfoI.gPLCControl, 0);
                SetStageGlobleI((int)GlobalinfoI.gBFCalControl, 0); //gConcurrence
                SetStageGlobleI((int)GlobalinfoI.gConcurrence, 0);
                SetStageGlobleI((int)GlobalinfoI.gStopInspectAF, 1);
                _runFlag = false;
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }

        /// <summary>
        /// EFEM手指伸出EFEM至Stage，信号输出为OFF stage不能动
        /// </summary>
        /// <returns></returns>
        public bool IsEFEMInterLockOutEnable()
        {
            try { return (GetIO("Z", _stageIOPara._EFEMInterLockOut)); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool IsEFEMInterLockOutEnable(int taskID)
        {
            try { return (GetIO("Z", _stageIOPara._EFEMInterLockOut, taskID)); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        /// <summary>
        /// stage到达上下料点位时，信号输出为ON，EFEM手指可以伸出
        /// </summary>
        /// <param name="enable"></param>
        public void SetEFEMInterLockIn(bool enable)
        {
            try
            {
                if (!enable)
                {
                    SetIO("Z", _stageIOPara._EFEMInterLokcIn, false);
                    return;
                }
                string error;
                //判断是否在装载位置
                double[] aXYZPosition = new double[3] { 0, 0, 0 };
                StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);

                aXYZPosition[0] = result.Axis[AxisStatusItem.PositionFeedback, "X"].Value;
                aXYZPosition[1] = result.Axis[AxisStatusItem.PositionFeedback, "Z"].Value;
                aXYZPosition[2] = result.Axis[AxisStatusItem.PositionFeedback, "Theta"].Value;
                //判断不在上下料位置则需要防呆处理
                if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) > 0.1)
                {
                    error = "ZCurrentPos:" + aXYZPosition[1].ToString("F4") + "!=" + "ZloadPos:" + _stageRunPara._ZLoadPos.ToString("F4");
                    RecordLog(error);
                    SetIO("Z", _stageIOPara._EFEMInterLokcIn, false);
                    throw new Exception(error);
                }
                if (Math.Abs(aXYZPosition[0] - _stageRunPara._XLoadPos) > 0.1)
                {
                    error = "XCurrentPos:" + aXYZPosition[0].ToString("F4") + "!=" + "XloadPos:" + _stageRunPara._XLoadPos.ToString("F4");
                    RecordLog(error);
                    SetIO("Z", _stageIOPara._EFEMInterLokcIn, false);
                    throw new Exception(error);
                }
                SetIO("Z", _stageIOPara._EFEMInterLokcIn, enable);
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool IsEFEMInterLockInEnable()
        {
            try { return GetIOOut("Z", _stageIOPara._EFEMInterLokcIn); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool IsSpiralRunControlEnable() 
        {
            try { return GetIOOut("Z", _stageIOPara._SpiralRunFlag); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        /// <summary>
        /// 判断是否在上下料位置
        /// </summary>
        private bool IsOnLoadPos()
        {
            try
            {
                double[] aXYZPosition = new double[3] { 0, 0, 0 };
                StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);

                aXYZPosition[0] = result.Axis[AxisStatusItem.PositionFeedback, "X"].Value;
                aXYZPosition[1] = result.Axis[AxisStatusItem.PositionFeedback, "Z"].Value;
                aXYZPosition[2] = result.Axis[AxisStatusItem.PositionFeedback, "Theta"].Value;
                //判断不在上下料位置则需要防呆处理
                if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) > 0.5)
                {
                    return false;
                }
                if (Math.Abs(aXYZPosition[0] - _stageRunPara._XLoadPos) > 0.5)
                {
                    return false;
                }
                if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 0.5)
                {
                    return false;
                }
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool GOpenInspectDoor() 
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    return OpenInspectDoor(4,true);
                }
                else
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                        error = "The current action of stage is in progress, Please wait";
                    else
                        error = "Stage当前动作正在进行中，请等待";
                    RecordLog(error);
                    throw new Exception(error);
                }
            }
            finally
            {
                if (hasLock)
                    Monitor.Exit(_mux);
            }
        }
        public bool OpenInspectDoor(bool wait = true)
        {
            if(!_OpenFlag)
                return true;
            try
            {
                string error;
                if (_runFlag) 
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Scanning in progress Please Wait");
                    else
                        throw new Exception("扫描正在进行中，请等待");
                }
                if (!IsEFEMInterLockOutEnable())
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                    else
                        throw new Exception(StageErrorInfoZ.触发EFEM互锁.ToString());
                }
                if (!IsInspectDoorOpen())
                {
                    if (wait)
                    {
                        SetIO("Z", _stageIOPara._InspectDoorOpenControl, true);
                        SetIO("Z", _stageIOPara._InspectDoorCloseControl, false);
                        int counter = 0;
                        while (!IsInspectDoorOpen())
                        {
                            SetIO("Z", _stageIOPara._InspectDoorOpenControl, true);
                            SetIO("Z", _stageIOPara._InspectDoorCloseControl, false);
                            Thread.Sleep(50);
                            counter++;
                            if (counter > 400)
                            {
                                if (_languageMode == LanguageMode.EN)
                                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.DetectionChamberOpenCloseDoorFault];
                                else
                                    error = StageErrorInfoZ.检测腔室开关门故障.ToString();
                                RecordLog(error);
                                throw new Exception(error);
                            }
                        }
                        return true;
                    }
                    else
                    {
                        SetIO("Z", _stageIOPara._InspectDoorOpenControl, true);
                        SetIO("Z", _stageIOPara._InspectDoorCloseControl, false);
                    }
                }
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool OpenInspectDoor(int taskID, bool wait = true)
        {
            if (!_OpenFlag)
                return true;
            try
            {
                string error;
                if (_runFlag)
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Scanning in progress Please Wait");
                    else
                        throw new Exception("扫描正在进行中，请等待");
                }
                if (!IsEFEMInterLockOutEnable(4))
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                    else
                        throw new Exception(StageErrorInfoZ.触发EFEM互锁.ToString());
                }
                if (!IsInspectDoorOpen(taskID))
                {
                    if (wait)
                    {
                        SetIO("Z", _stageIOPara._InspectDoorOpenControl, true, taskID);
                        SetIO("Z", _stageIOPara._InspectDoorCloseControl, false, taskID);
                        int counter = 0;
                        while (!IsInspectDoorOpen(taskID))
                        {
                            SetIO("Z", _stageIOPara._InspectDoorOpenControl, true, taskID);
                            SetIO("Z", _stageIOPara._InspectDoorCloseControl, false, taskID);
                            Thread.Sleep(50);
                            counter++;
                            if (counter > 400)
                            {
                                if (_languageMode == LanguageMode.EN)
                                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.DetectionChamberOpenCloseDoorFault];
                                else
                                    error = StageErrorInfoZ.检测腔室开关门故障.ToString();
                                RecordLog(error);
                                throw new Exception(error);
                            }
                        }
                        return true;
                    }
                    else
                    {
                        SetIO("Z", _stageIOPara._InspectDoorOpenControl, true, taskID);
                        SetIO("Z", _stageIOPara._InspectDoorCloseControl, false, taskID);
                    }
                }
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool[] InspectDoolEnableState()
        {
            try
            {
                bool[] state = new bool[2];
                state[0] = GetIOOut("Z", _stageIOPara._InspectDoorOpenControl);
                state[1] = GetIOOut("Z", _stageIOPara._InspectDoorCloseControl);
                return state;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }

        public bool GCloseInspectDoor() 
        {
            bool hasLock = false;
            try
            {
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    return CloseInspectDoor(4,true);
                }
                else
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                        error = "The current action of stage is in progress, Please wait";
                    else
                        error = "Stage当前动作正在进行中，请等待";
                    RecordLog(error);
                    throw new Exception(error);
                }
            }
            finally
            {
                if (hasLock)
                    Monitor.Exit(_mux);
            }
        }
        public bool CloseInspectDoor(bool wait = true) 
        {
            if (!_OpenFlag)
                return true;
            try
            {
                if (_runFlag)
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Scanning in progress Please Wait");
                    else
                        throw new Exception("扫描正在进行中，请等待");
                }
                string error;
                if (!IsEFEMInterLockOutEnable())
                {
                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock];
                    RecordLog(error);
                    throw new Exception(error);
                }
                if (!IsInspectDoorClose())
                {
                    if (wait)
                    {
                        SetIO("Z", _stageIOPara._InspectDoorOpenControl, false);
                        SetIO("Z", _stageIOPara._InspectDoorCloseControl, true);
                        int counter = 0;
                        while (!IsInspectDoorClose())
                        {
                            SetIO("Z", _stageIOPara._InspectDoorOpenControl, false);
                            SetIO("Z", _stageIOPara._InspectDoorCloseControl, true);
                            Thread.Sleep(50);
                            counter++;
                            if (counter > 400)
                            {
                                if (_languageMode == LanguageMode.EN)
                                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.DetectionChamberOpenCloseDoorFault];
                                else
                                    error = StageErrorInfoZ.检测腔室开关门故障.ToString();
                                RecordLog(error);
                                throw new Exception(error);
                            }
                        }
                        return true;
                    }
                    else
                    {
                        SetIO("Z", _stageIOPara._InspectDoorOpenControl, false);
                        SetIO("Z", _stageIOPara._InspectDoorCloseControl, true);
                    }
                }
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool CloseInspectDoor(int taskID, bool wait = true)
        {
            if (!_OpenFlag)
                return true;
            try
            {
                if (_runFlag)
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception("Scanning in progress Please Wait");
                    else
                        throw new Exception("扫描正在进行中，请等待");
                }
                string error;
                if (!IsEFEMInterLockOutEnable())
                {
                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock];
                    RecordLog(error);
                    throw new Exception(error);
                }
                if (!IsInspectDoorClose())
                {
                    if (wait)
                    {
                        SetIO("Z", _stageIOPara._InspectDoorOpenControl, false);
                        SetIO("Z", _stageIOPara._InspectDoorCloseControl, true);
                        int counter = 0;
                        while (!IsInspectDoorClose())
                        {
                            SetIO("Z", _stageIOPara._InspectDoorOpenControl, false);
                            SetIO("Z", _stageIOPara._InspectDoorCloseControl, true);
                            Thread.Sleep(50);
                            counter++;
                            if (counter > 400)
                            {
                                if (_languageMode == LanguageMode.EN)
                                    error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.DetectionChamberOpenCloseDoorFault];
                                else
                                    error = StageErrorInfoZ.检测腔室开关门故障.ToString();
                                RecordLog(error);
                                throw new Exception(error);
                            }
                        }
                        return true;
                    }
                    else
                    {
                        SetIO("Z", _stageIOPara._InspectDoorOpenControl, false);
                        SetIO("Z", _stageIOPara._InspectDoorCloseControl, true);
                    }
                }
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool IsInspectDoorOpen()
        {
            if (!_OpenFlag)
                return true;
            try { return (GetIO("Z", _stageIOPara._InspectDoorOpen) && !GetIO("Z", _stageIOPara._InspectDoorClose)); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool IsInspectDoorOpen(int taskID)
        {
            if (!_OpenFlag)
                return true;
            try { return (GetIO("Z", _stageIOPara._InspectDoorOpen, taskID) && !GetIO("Z", _stageIOPara._InspectDoorClose, taskID)); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool IsInspectDoorClose() 
        {
            if (!_OpenFlag)
                return true;
            try { return (GetIO("Z", _stageIOPara._InspectDoorClose) && !GetIO("Z", _stageIOPara._InspectDoorOpen)); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool IsInspectDoorClose(int taskID)
        {
            if (!_OpenFlag)
                return true;
            try { return (GetIO("Z", _stageIOPara._InspectDoorClose, taskID) && !GetIO("Z", _stageIOPara._InspectDoorOpen, taskID)); }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public void RecordLog(string info) 
        {
            // 获取今天的日期，用于生成日志文件名
            string today = DateTime.Now.ToString("yyyy-MM-dd");
            string logDirectoryPath = Path.Combine(System.Windows.Forms.Application.StartupPath, "StageLog");
            // 检查文件夹是否存在，如果不存在则创建
            if (!Directory.Exists(logDirectoryPath))
            {
                Directory.CreateDirectory(logDirectoryPath);
            }
            string logFilePath = Path.Combine(logDirectoryPath, $"Stage_{today}.log");
            try 
            {
                File.AppendAllText(logFilePath, $"{DateTime.Now}:{info}\n");
            }
            catch (Exception ex) { throw new Exception(ex.Message + info); }
        }
        /// <summary>
        /// 获取Stage控制器里的扫描脚本库版本
        /// </summary>
        /// <returns></returns>
        /// <exception cref="Exception"></exception>
        public string GetScriptVersion() 
        {
            try
            {
                _stageRunPara._ScriptVersion = GetStageGlobleStr((int)GlobalinfoStr.gScriptVersion);
                return _stageRunPara._ScriptVersion;
            }
            catch(Exception e) 
            {
                RecordLog(e.Message);
                throw new Exception(e.Message);
            }
        }
        private void WaitMotionDone(string axisName) 
        {
            //need check input para
            try
            {
                _controller.Runtime.Commands.Motion.WaitForMotionDone(axisName);
                StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);
                AxisFault axisFault = (AxisFault)result.Axis[AxisStatusItem.AxisFault, axisName].Value;
                if (axisFault != AxisFault.None)
                {
                    throw new Exception("Axis:" + axisName + " "+axisFault.ToString());
                }
                DriveStatus driveStatus = (DriveStatus)result.Axis[AxisStatusItem.DriveStatus, axisName].Value;
                //if ( !driveStatus.HasFlag(DriveStatus.InPosition))
                //{
                //    throw new Exception(axisName + "Axis:" + "Not " + DriveStatus.InPosition.ToString());
                //}
                if (!driveStatus.HasFlag(DriveStatus.Enabled))
                {
                    throw new Exception("Axis:" + axisName +  " Not " + DriveStatus.Enabled.ToString());
                }
            }
            catch (Exception ex) 
            {
                throw new Exception(ex.Message);
            }
        }
        private void WaitMotionDone(string[] axisNames) 
        {
            try
            {
                _controller.Runtime.Commands.Motion.WaitForMotionDone(axisNames);
                foreach (string axisName in axisNames)
                {
                   
                    StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);
                    AxisFault axisFault = (AxisFault)result.Axis[AxisStatusItem.AxisFault, axisName].Value;
                    if (axisFault != AxisFault.None)
                    {
                        throw new Exception("Axis:" + axisName + " " +axisFault.ToString());
                    }
                    DriveStatus driveStatus = (DriveStatus)result.Axis[AxisStatusItem.DriveStatus, axisName].Value;
                    //if (!driveStatus.HasFlag(DriveStatus.InPosition))
                    //{
                    //    throw new Exception(axisName + "Axis:" + "Not " + DriveStatus.InPosition.ToString());
                    //}
                    if (!driveStatus.HasFlag(DriveStatus.Enabled))
                    {
                        throw new Exception("Axis:" + axisName + " Not " + DriveStatus.Enabled.ToString());
                    }
                }
            }
            catch (Exception ex)
            {
                throw new Exception(ex.Message);
            }
        }
        /// <summary>
        /// 测试：读取窗口触发设定前的输入角度
        /// </summary>
        /// <returns></returns>
        private void  GetBeforeDriveAngles()
        {
            try
            {
                List<double> angles = new List<double>();
                string psoAngles = "DriveWritePSOAngles:";
                for (int i = 0; i < _stageRunPara._CircleNum + 1; ++i)
                {
                    if (i == 0)
                    {
                        psoAngles = psoAngles + " 0";
                        psoAngles = psoAngles + " "+ GetStageGlobleR((int)GlobalInfo.gCircleAngleStart + i);
                    }
                    else if (i == _stageRunPara._CircleNum)
                    {
                        psoAngles = psoAngles + " " + GetStageGlobleR((int)GlobalInfo.gCircleAngleStart + i);
                        psoAngles = psoAngles + " " + (GetStageGlobleR((int)GlobalInfo.gCircleAngleStart + i) + 540);
                    }
                    else
                    {
                        psoAngles = psoAngles + " " + GetStageGlobleR((int)GlobalInfo.gCircleAngleStart + i);
                        psoAngles = psoAngles + " " + (GetStageGlobleR((int)GlobalInfo.gCircleAngleStart + i) + 450);
                    }
                }
                RecordLog(psoAngles);
            }
            catch(Exception ex) { RecordLog(ex.Message); throw ex; }
            
        }
        private void  GetAfterDriveAngles()
        {
            try
            {
                string psoAngles = "DriveReadyPSOAngles:";
                for (int i = 0; i < _stageRunPara._CircleNum + 1; ++i)
                {

                    psoAngles = psoAngles + " 0";
                    psoAngles = psoAngles + " " + ((int)GlobalInfo.gCircleAngleStart + 30 + 2 * i);
                    psoAngles = psoAngles + " " + GetStageGlobleR((int)GlobalInfo.gCircleAngleStart + 30 + 2 * i + 1);

                }
                RecordLog(psoAngles);
            }
            catch(Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        private bool isAxisNormal()
        {
            try
            {
                StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);
                AxisFault t = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "Theta"].Value;
                if (t != AxisFault.None)
                {
                    _controller.Runtime.Tasks[1].Program.Stop();
                    return false;
                }
                AxisFault x = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "X"].Value;
                if (x != AxisFault.None)
                {
                    _controller.Runtime.Tasks[1].Program.Stop();
                    return false;
                }
                AxisFault z = (AxisFault)result.Axis[AxisStatusItem.AxisFault, "Z"].Value;
                if (z != AxisFault.None)
                {
                    _controller.Runtime.Tasks[1].Program.Stop();
                    return false;
                }
                return true;
            }
            catch (Exception e) { RecordLog(e.Message); throw e; }
        }
        public bool StopRun()
        {
            try
            {
                SetStageGlobleI((int)GlobalinfoI.gStop, 1);
				return true;
            }
            catch (Exception e)
            {
                ResetState();
                RecordLog(e.Message);
                throw new Exception(e.Message);
            }
        }

        const int wafer68 = 68;
        const int wafer812 = 812;
        private void ChangePinPosWithSize()
        {
            if (_stageRunPara._CompatibleWaferSize == wafer68)
            {
                if (_stageRunPara._WaferSize == 6)
                {
                    SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, true);
                    SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, false);
                    Thread.Sleep(10);
                    int counter = 0;
                    while (!GetIO("Theta", _stageIOPara._PinWithSizePosSmall))
                    {
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, true);
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, false);
                        Thread.Sleep(10);
                        counter++;
                        if (counter > MAXNUM)
                            break;
                    }
                    if (counter > MAXNUM)
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinSizePostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN尺寸位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    counter = 0;
                    while (GetIO("Theta", _stageIOPara._PinWithSizePosSmall))
                    {
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, true);
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, false);
                        Thread.Sleep(10);
                        counter++;
                        if (counter > 3)
                            break;
                    }
                    if(counter <= 3) 
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinSizePostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN尺寸位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
                if (_stageRunPara._WaferSize == 8)
                {
                    SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, false);
                    SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, true);
                    Thread.Sleep(10);
                    int counter = 0;
                    while (!GetIO("Theta", _stageIOPara._PinWithSizePosBig))
                    {
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, false);
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, true);
                        Thread.Sleep(10);
                        counter++;
                        if (counter > MAXNUM)
                            break;
                    }
                    if (counter > MAXNUM)
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinSizePostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN尺寸位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    counter = 0;
                    while (GetIO("Theta", _stageIOPara._PinWithSizePosBig))
                    {
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, false);
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, true);
                        Thread.Sleep(50);
                        counter++;
                        if (counter > 3)
                            break;
                    }
                    if(counter <= 3) 
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinSizePostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN尺寸位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
                else 
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception($"ReipeWaferSizeFault:{_stageRunPara._WaferSize} inch ");
                    else
                        throw new Exception($"配方晶圆尺寸故障{_stageRunPara._WaferSize}寸");
                }
            }
            if (_stageRunPara._CompatibleWaferSize == wafer812)
            {
                if (_stageRunPara._WaferSize == 8)
                {
                    SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, true);
                    SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, false);
                    Thread.Sleep(10);
                    int counter = 0;
                    while (!GetIO("Theta", _stageIOPara._PinWithSizePosSmall))
                    {
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, true);
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, false);
                        Thread.Sleep(10);
                        counter++;
                        if (counter > MAXNUM)
                            break;
                    }
                    if (counter > MAXNUM)
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinSizePostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN尺寸位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    counter = 0;
                    while (GetIO("Theta", _stageIOPara._PinWithSizePosSmall))
                    {
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, true);
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, false);
                        Thread.Sleep(50);
                        counter++;
                        if (counter > 3)
                            break;
                    }
                    if(counter <= 3) 
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinSizePostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN尺寸位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
                if (_stageRunPara._WaferSize == 12)
                {
                    SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, false);
                    SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, true);
                    Thread.Sleep(10);
                    int counter = 0;
                    while (!GetIO("Theta", _stageIOPara._PinWithSizePosBig))
                    {
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, false);
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, true);
                        Thread.Sleep(10);
                        counter++;
                        if (counter > MAXNUM)
                            break;
                    }
                    if (counter > MAXNUM)
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinSizePostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN尺寸位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    counter = 0;
                    while (GetIO("Theta", _stageIOPara._PinWithSizePosBig))
                    {
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeSmallControl, false);
                        SetIO("Theta", _stageIOPara._PinWithSizePosChangeBigControl, true);
                        Thread.Sleep(50);
                        counter++;
                        if (counter > 3)
                            break;
                    }
                    if(counter <= 3) 
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinSizePostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN尺寸位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
                else 
                {
                    if (_languageMode == LanguageMode.EN)
                        throw new Exception($"ReipeWaferSizeFault:{_stageRunPara._WaferSize} inch ");
                    else
                        throw new Exception($"配方晶圆尺寸故障{_stageRunPara._WaferSize}寸");
                }
            }
        }
        private void ChangePinPosWithInitAvoidance(bool flag, bool wait = true)
        {
            if (flag)
            {
                SetIO("Theta", _stageIOPara._PinAvoidPosChangeControl, true);
                SetIO("Theta", _stageIOPara._PinNormalPosChangeControl, false);
                if (wait)
                {
                    Thread.Sleep(10);
                    int counter = 0;
                    while (!GetIO("Theta", _stageIOPara._PinAvoidZInitPos))
                    {
                        SetIO("Theta", _stageIOPara._PinAvoidPosChangeControl, true);
                        SetIO("Theta", _stageIOPara._PinNormalPosChangeControl, false);
                        Thread.Sleep(10);
                        counter++;
                        if (counter > MAXNUM)
                            break;
                    }
                    if (counter > MAXNUM)
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinAvoidPostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN避让位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    counter = 0;
                    while (GetIO("Theta", _stageIOPara._PinAvoidZInitPos))
                    {
                        SetIO("Theta", _stageIOPara._PinAvoidPosChangeControl, true);
                        SetIO("Theta", _stageIOPara._PinNormalPosChangeControl, false);
                        Thread.Sleep(50);
                        counter++;
                        if (counter > 3)
                            break;
                    }
                    if (counter <= 3) 
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinAvoidPostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN避让位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
            }
            else
            {
                SetIO("Theta", _stageIOPara._PinAvoidPosChangeControl, false);
                SetIO("Theta", _stageIOPara._PinNormalPosChangeControl, true);
                if (wait)
                {
                    Thread.Sleep(10);
                    int counter = 0;
                    while (!GetIO("Theta", _stageIOPara._PinNormalPos))
                    {
                        SetIO("Theta", _stageIOPara._PinAvoidPosChangeControl, false);
                        SetIO("Theta", _stageIOPara._PinNormalPosChangeControl, true);
                        Thread.Sleep(10);
                        counter++;
                        if (counter > MAXNUM)
                            break;
                    }
                    if (counter > MAXNUM)
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinAvoidPostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN避让位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                    counter = 0;
                    while (GetIO("Theta", _stageIOPara._PinNormalPos))
                    {
                        SetIO("Theta", _stageIOPara._PinAvoidPosChangeControl, false);
                        SetIO("Theta", _stageIOPara._PinNormalPosChangeControl, true);
                        Thread.Sleep(50);
                        counter++;
                        if (counter > 3)
                            break;
                    }
                    if(counter <= 3) 
                    {
                        string error;
                        if (_languageMode == LanguageMode.EN)
                            error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.ChangePinAvoidPostionFault];
                        else
                            error = StageErrorInfoZ.改变PIN避让位置故障.ToString();
                        RecordLog(error);
                        throw new Exception(error);
                    }
                }
            }
        }
        /// <summary>
        /// 查询是否在避让位置
        /// </summary>
        /// <returns></returns>
        private bool isPinInAvoidPos()
        {
            try
            {
                if (GetIO("Theta", _stageIOPara._PinAvoidZInitPos) && !GetIO("Theta", _stageIOPara._PinNormalPos))
                {
                    return true;
                }
                else if (!GetIO("Theta", _stageIOPara._PinAvoidZInitPos) && GetIO("Theta", _stageIOPara._PinNormalPos))
                {
                    return false;
                }
                else
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.PinAvoidPositionFault];
                    else
                        error = StageErrorInfoZ.Pin避让位置异常.ToString();
                    RecordLog(error);
                    throw new Exception(error);
                }
            }
            catch (Exception ex)
            {
                RecordLog(ex.Message);
                throw ex;
            }
        }
        /// <summary>
        /// 查询Pin尺寸位置
        /// </summary>
        /// <returns></returns>
        private bool isPinInBigPos()
        {
            try
            {
                if (GetIO("Theta", _stageIOPara._PinWithSizePosBig) && !GetIO("Theta", _stageIOPara._PinWithSizePosSmall))
                {
                    return true;
                }
                else if (!GetIO("Theta", _stageIOPara._PinWithSizePosBig) && GetIO("Theta", _stageIOPara._PinWithSizePosSmall))
                {
                    return false;
                }
                else
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                        error = StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.PinSizePositionFault];
                    else
                        error = StageErrorInfoZ.Pin尺寸位置异常.ToString();
                    RecordLog(error);
                    throw new Exception(error);
                }
            }
            catch (Exception ex)
            {
                RecordLog(ex.Message);
                throw ex;
            }
        }
        private void CompareWaferSizePosWithRecipe()
        {
            try
            {
                if (IsWaferExist())
                {
                    if ((_stageRunPara._WaferSize == 6) && (isBigWaferExist()))
                    {
                        if (_languageMode == LanguageMode.EN)
                            throw new Exception($"Reipe WaferSize:{_stageRunPara._WaferSize} inch  not match the real Wafer Size: 8 inch ");
                        else
                            throw new Exception($"配方晶圆尺寸：{_stageRunPara._WaferSize}寸与实际晶圆尺寸:8寸不匹配");
                    }
                    else if ((_stageRunPara._WaferSize == 8) && (!isBigWaferExist()))
                    {
                        if (_languageMode == LanguageMode.EN)
                            throw new Exception($"Reipe WaferSize:{_stageRunPara._WaferSize} inch  not match the real Wafer Size: 6 inch ");
                        else
                            throw new Exception($"配方晶圆尺寸：{_stageRunPara._WaferSize}寸与实际晶圆尺寸:6寸不匹配");
                    }
                    else {; }
                }
                else 
                {
                    if ((_stageRunPara._WaferSize == 6) && !isPinInBigPos())
                    {
                        ;
                    }
                    else if ((_stageRunPara._WaferSize == 8) && isPinInBigPos())
                    {
                        ;
                    }
                    else
                    {
                         ChangePinPosWithSize();
                    }
                }
            }
            catch(Exception ex) { RecordLog(ex.Message); throw ex; }
        }
        private void CheckIfChangePinSizePos(bool change = true) 
        {
            try
            {
                if (!IsWaferExist())
                {
                    if ((_stageRunPara._WaferSize == 6) && !isPinInBigPos())
                    {
                        ;
                    }
                    else if ((_stageRunPara._WaferSize == 8) && isPinInBigPos())
                    {
                        ;
                    }
                    else
                    {
                        if (change)
                        {
                            ChangePinPosWithSize();
                        }
                    }
                }
                else
                {
                    if (isBigWaferExist() && isPinInBigPos())
                    {
                        ;//正常
                    }
                    else if (!isBigWaferExist() && !isPinInBigPos())
                    {
                        ;//正常
                    }
                   
                    else if (isBigWaferExist() && !isPinInBigPos())
                    {
                        if (_languageMode == LanguageMode.EN)
                            throw new Exception($"Wafer Size:8 inch  not match Pin Position: 6 inch Position");
                        else
                            throw new Exception($"晶圆尺寸8寸与Pin位置:6寸位置不匹配");
                    }
                    else if (!isBigWaferExist() && isPinInBigPos())
                    {
                        if (_languageMode == LanguageMode.EN)
                            throw new Exception($"Wafer Size:6 inch  not match Pin Position: 8 inch Position");
                        else
                            throw new Exception($"晶圆尺寸6寸与Pin位置:8寸位置不匹配");
                    }
                    else {; }
                    if (change) 
                    {
                        if (_stageRunPara._WaferSize == 6 && isPinInBigPos())
                        {
                            if (_languageMode == LanguageMode.EN)
                                throw new Exception($"Has Wafer,Recipe Wafer Size:8 inch  not match Pin Position: 8 inch Position");
                            else
                                throw new Exception($"有晶圆，配方晶圆尺寸6寸与Pin位置:8寸位置不匹配");
                        }
                        else if (_stageRunPara._WaferSize == 8 && !isPinInBigPos())
                        {
                            if (_languageMode == LanguageMode.EN)
                                throw new Exception($"Has Wafer,Recipe Wafer Size:8 inch  not match Pin Position: 6 inch Position");
                            else
                                throw new Exception($"有晶圆，配方晶圆尺寸8寸与Pin位置:6寸位置不匹配");
                        }
                        else {; }
                    }
                }
            }
            catch(Exception ex) { RecordLog(ex.Message);throw ex; }
        }
        public  bool Seperate() 
        {
            if (_runFlag)
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception("Scanning in progress Please Wait");
                else
                    throw new Exception("扫描正在进行中，请等待");
            }
            bool hasLock = false;
            try
            {
                if (!IsEFEMInterLockOutEnable(4))
                {
                    //if (IsOnLoadPos())
                    //    SetEFEMInterLockIn(true);
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                }
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    
                    SetEFEMInterLockIn(false);
                    //开门
                    OpenInspectDoor(false);
                    //判断是否在装载位置
                    double[] aXYZPosition = new double[3] { 0, 0, 0 };
                    StatusItemResults result = _controller.Runtime.Status.GetStatusItems(_statusItemConfiguration);

                    aXYZPosition[0] = result.Axis[AxisStatusItem.PositionFeedback, "X"].Value;
                    aXYZPosition[1] = result.Axis[AxisStatusItem.PositionFeedback, "Z"].Value;
                    aXYZPosition[2] = result.Axis[AxisStatusItem.PositionFeedback, "Theta"].Value;
                    switch (_WaferUpDownMode)
                    {
                        case WaferUpDownMode.UpDownPinInChhuck:
                        case WaferUpDownMode.UpDownPinOutChuck:
                            {
                                //判断不在上下料位置则需要防呆处理
                                if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) > 0.5)
                                {
                                    if (IsPinUp())
                                    {
                                        if (!DownPin())
                                            return false;
                                    }
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("Z", _stageRunPara._ZLoadPos, 50);
                                }
                                if (Math.Abs(aXYZPosition[0] - _stageRunPara._XLoadPos) > 0.5)
                                {
                                    if (IsPinUp())
                                    {
                                        if (!DownPin())
                                            return false;
                                    }
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("X", _stageRunPara._XLoadPos, 160);
                                }
                                if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 0.5)
                                {
                                    if (IsPinUp())
                                    {
                                        if (!DownPin())
                                            return false;
                                    }
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 360)
                                        homeAxis("Theta");
                                    MoveAxis("Theta", _stageRunPara._TLoadPos, 600);
                                }
                               
                                if (!Release())
                                    return false;
                                //if (!UpPin())
                                //    return false;
                                if (!UpPinFast())
                                    return false;
                                OpenInspectDoor(true);
                                SetEFEMInterLockIn(true);
                                return true;
                            }
                            break;
                        case WaferUpDownMode.UpDownChuckFixPin:
                        case WaferUpDownMode.UpDownChuckFixPinNoAvoid:
                            {
                                //判断不在上下料位置则需要防呆处理
                                //if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) > 0.5)
                                //{
                                //    if (IsPinUp())
                                //    {
                                //        if (!DownPin())
                                //            return false;
                                //    }
                                //    if (IsWaferExist())
                                //    {
                                //        if (!Fix())
                                //            return false;
                                //    }
                                //    MoveAxis("Z", _stageRunPara._ZLoadPos, 50);
                                //}
                                if (Math.Abs(aXYZPosition[0] - _stageRunPara._XLoadPos) > 0.5)
                                {
                                    //if (IsPinUp())
                                    //{
                                    //    if (!DownPin())
                                    //        return false;
                                    //}
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("X", _stageRunPara._XLoadPos, 160);
                                }
                                if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 0.5)
                                {
                                    //if (IsPinUp())
                                    //{
                                    //    if (!DownPin())
                                    //        return false;
                                    //}
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 360)
                                        homeAxis("Theta");
                                    MoveAxis("Theta", _stageRunPara._TLoadPos, 600);
                                }
                                //if (!Release())
                                //    return false;
                                //if (!UpPin())
                                //    return false;
                                DateTime upS = DateTime.Now;
                                //if (!UpPinFast())
                                //    return false;
                                if (!DownChuck())
                                    return false;
                                OpenInspectDoor(true);
                                SetEFEMInterLockIn(true);
                                return true;
                            }
                            break;
                        case WaferUpDownMode.UpDownFixPinAndChuck:
                            {
                                //判断不在上下料位置则需要防呆处理
                                if (Math.Abs(aXYZPosition[1] - _stageRunPara._ZLoadPos) > 0.5)
                                {
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("Z", _stageRunPara._ZLoadPos, 50);
                                }
                                if (Math.Abs(aXYZPosition[0] - _stageRunPara._XLoadPos) > 0.5)
                                {
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    MoveAxis("X", _stageRunPara._XLoadPos, 160);
                                }
                                if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 0.5)
                                {
                                    if (IsWaferExist())
                                    {
                                        if (!Fix())
                                            return false;
                                    }
                                    if (Math.Abs(aXYZPosition[2] - _stageRunPara._TLoadPos) > 360)
                                        homeAxis("Theta");
                                    MoveAxis("Theta", _stageRunPara._TLoadPos, 600);
                                }
                                if (!Release())
                                    return false;
                                //if (!UpPin())
                                //    return false;
                                //if (!UpPinFast())
                                //    return false;
                                OpenInspectDoor(true);
                                SetEFEMInterLockIn(true);
                                return true;
                            }
                            break;
                        default:
                            {
                                string error = "The lifting method for the wafer has not been configured";
                                RecordLog(error);
                                throw new Exception(error);
                            }
                            break;
                    }
                }
                else
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                        error = "The current action of stage is in progress, Please wait";
                    else
                        error = "Stage当前动作正在进行中，请等待";
                    RecordLog(error);
                    throw new Exception(error);
                }
            }
            finally
            {
                if (hasLock)
                    Monitor.Exit(_mux);
            }
        }
        public bool Merge() 
        {
            if (_runFlag)
            {
                if (_languageMode == LanguageMode.EN)
                    throw new Exception("Scanning in progress Please Wait");
                else
                    throw new Exception("扫描正在进行中，请等待");
            }
            bool hasLock = false;
            try
            {
                if (!IsEFEMInterLockOutEnable(4))
                {
                    //if (IsOnLoadPos())
                    //    SetEFEMInterLockIn(true);
                    throw new Exception(StageErrorInfoEE.StageErrorInfos[(int)StageErrorInfoE.TriggerEFEMInterLock]);
                }
                if (Monitor.TryEnter(_mux, 30000))
                {
                    hasLock = true;
                    switch (_WaferUpDownMode)
                    {
                        case WaferUpDownMode.UpDownPinInChhuck:
                        case WaferUpDownMode.UpDownPinOutChuck:
                            {
                                if (!HasWaferFix())
                                {
                                    return false;
                                }
                            }
                            break;
                        case WaferUpDownMode.UpDownChuckFixPin:
                            {
                                if (!UpChuck())
                                {
                                    return false;
                                }
                                if (!isPinInAvoidPos())
                                {
                                    ChangePinPosWithInitAvoidance(true, false);
                                }
                            }
                            break;
                        case WaferUpDownMode.UpDownChuckFixPinNoAvoid:
                            {
                                if (!UpChuck())
                                {
                                    return false;
                                }
                            }
                            break;
                        case WaferUpDownMode.UpDownFixPinAndChuck:
                            {

                            }
                            break;
                        default:
                            {

                            }
                            break;
                    }
                }
                else
                {
                    string error;
                    if (_languageMode == LanguageMode.EN)
                        error = "The current action of stage is in progress, Please wait";
                    else
                        error = "Stage当前动作正在进行中，请等待";
                    RecordLog(error);
                    throw new Exception(error);
                }
            }
            finally
            {
                if (hasLock)
                    Monitor.Exit(_mux);
            }
            return true;
        }

        // Windows API functions for INI file handling
        [DllImport("kernel32.dll", CharSet = CharSet.Unicode)]
        static extern long WritePrivateProfileString(string section, string key, string value, string filePath);

        [DllImport("kernel32.dll", CharSet = CharSet.Unicode)]
        static extern int GetPrivateProfileString(string section, string key, string defaultValue, StringBuilder returnValue, int size, string filePath);

        private static readonly string IniFilePath = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "Stage.ini");
        private static int ReadLanguage()
        {
            if (!File.Exists(IniFilePath))
            {
                throw new FileNotFoundException($"INI file not found: {IniFilePath}");
            }

            const string section = "SetUp";
            const string key = "Language";
            const int size = 255;
            StringBuilder returnValue = new StringBuilder(size);

            GetPrivateProfileString(section, key, "", returnValue, size, IniFilePath);

            if (int.TryParse(returnValue.ToString(), out int language))
            {
                return language;
            }
            else
            {
                throw new FormatException("The Language value is not a valid integer.");
            }
        }

        private void CollectDataTest() 
        {
            Task.Run(() =>
            {
                DataCollectionConfiguration CollectData = new DataCollectionConfiguration(240000, 1);//采样点数，采样时间

                CollectData.Axis.Add(AxisDataSignal.PositionFeedback, "X");
                CollectData.Axis.Add(AxisDataSignal.PositionFeedback, "Theta");
                CollectData.Axis.Add(AxisDataSignal.PositionFeedback, "Z");
                CollectData.Axis.Add(AxisDataSignal.AnalogInput0, "Z");
                CollectData.System.Add(SystemDataSignal.DataCollectionSampleTime);
                CollectData.Task.Add(TaskDataSignal.TaskState, 3);//这个是获取任务状态的，从表面理解上不是绑定任务
                _RealStageData = _controller.Runtime.DataCollection.CollectSnapshot(CollectData);//这个是阻塞的直到数据采集完毕

                _controller.Runtime.DataCollection.Stop();//过程中可以停止
                double[] xp = _RealStageData.Axis[AxisDataSignal.PositionFeedback, "X"].Points;
                double[] yp = _RealStageData.Axis[AxisDataSignal.PositionFeedback, "Theta"].Points;
                double[] zp = _RealStageData.Axis[AxisDataSignal.PositionFeedback, "Z"].Points;
                double[] zv = _RealStageData.Axis[AxisDataSignal.AnalogInput0, "Z"].Points;
                double[] st = _RealStageData.System[SystemDataSignal.DataCollectionSampleTime].Points;
            });
            
        }
        private Tuple<double, double, double, double, double> GetStageAFData()
        {
            return new Tuple<double, double, double, double, double>(1, 2, 3, 4, 5);
        }
    }
    
    
    public class FPixelSizes
    {
        public  const double FDF8 = 0.0012;
        public  const double FBF8 = 0.0005;
        public  const double FDF112 = 0.0006;
        public  const double FDF212 = 0.0006;
        public  const double FDF312 = 0.0006;
        public  const double FDF412 = 0.0006;
        public  const double FBF12 = 0.0006;
    }
    public class FPixelCount
    {
        public  const int FDF8 = 4096;
        public  const int FBF8 = 8192;
        public  const int FDF112 = 4096;
        public  const int FDF212 = 4096;
        public  const int FDF312 = 4096;
        public  const int FDF412 = 4096;
        public  const int FBF12 = 4096;
    }
    public class StageRunPara 
    {
        /// <summary>
        /// 连接Stage的IP
        /// </summary>
        public string _IP;
        /// <summary>
        /// Stage脚本库绝对路径
        /// </summary>
        public string _SprialScriptPath;
        public string _StageConcurrencePath = "AKStageConcurrence.ascript";
        /// <summary>
        /// 取放片示教点位，注意旋转轴由于升降PIN，其位置是固定的角度，直线轴的单位是mm 旋转轴的单位是deg
        /// </summary>
        public double _XLoadPos;
        public double _ZLoadPos;
        public double _TLoadPos;
        /// <summary>
        /// Z轴的初始聚焦位置
        /// </summary>
        public double _ZInspecPos;
        /// <summary>
        /// 旋转起始点一般自行计算，暂时未启用
        /// </summary>
        public double _XSpiralStartPos;
        public double _ZSpiralStartPos;
        public double _TSpiralStartPos;
        /// <summary>
        /// 螺旋和同心圆间距 单位是mm
        /// </summary>
        public double _Fov = 0;
        /// <summary>
        /// 旋转进给半径：目前用的参数12寸154mm 8寸104mm
        /// </summary>
        public double _WaferWaferRadius;
        /// <summary>
        /// 物镜成像中心的Stage坐标 X轴 单位mm
        /// </summary>
        public double _SensorToOriginal = 0;
        /// <summary>
        /// 线扫触发行频：多通道以其中一个为基准
        /// </summary>
        public double _CameraLR;
        /// <summary>
        /// 像素尺寸 单位mm：多通道基准
        /// </summary>
        public double _PixelSize = 0;
        /// <summary>
        /// 相机扫描设置的每行像素个数：多通道基准
        /// </summary>
        public double _PixelCount = 0;
        /// <summary>
        /// 相机Bin参数：多通道基准
        /// </summary>
        public double _Binning = 0;
        /// <summary>
        /// 线扫触发行频：多通道基准
        /// </summary>
        public double _CameraLR2;
        /// <summary>
        /// 像素尺寸 单位mm：多通道以其中一个基准
        /// </summary>
        public double _PixelSize2;
        /// <summary>
        /// 像素个数：多通道以其中一个为基准
        /// </summary>
        public double _PixelCount2;
        /// <summary>
        /// 相机Bin参数：多通道以其中一个为基准
        /// </summary>
        public double _Binning2;
      
        /// <summary>
        /// Stage运行状态
        /// </summary>
        public int _StageState;
        /// <summary>
        /// Stage运行是否负载Wafer
        /// </summary>
        public int _SpiralWithWaferFlag = 1;
        /// <summary>
        /// 螺旋+同心圆的触发角度 单位deg
        /// </summary>
        public List<double> _CircleAngles;
        /// <summary>
        /// 同心圆圈数
        /// </summary>
        public int _CircleNum;
        /// <summary>
        /// AF启用标志
        /// </summary>
        public int _AFControlFlag = 0;
        /// <summary>
        /// AF反馈轴"X""Theta""Z"
        /// </summary>
        public string _AFVaxisName = "Z";
        public string _AFVSumaxisName = "X";
        /// <summary>
        /// AF 电压与距离的线性函数斜率
        /// </summary>
        public double _AFLinearFunSlope = 0;
        /// <summary>
        /// AF 电压与距离的线性函数截距
        /// </summary>
        public double _AFLinearFunIntercept = 0;
        /// <summary>
        /// 用于判断是否可以读取AF值
        /// </summary>
        public double AFSumThreshold = 0;
        /// <summary>
        /// AF电压基准
        /// </summary>
        public double _AFVBase = 0;
        /// <summary>
        /// AF电压基准偏移：用于不同材质的矫正
        /// </summary>
        public double _AFVOffset = 0;
        /// <summary>
        /// X用圆心位置
        /// </summary>
        public double _AFCalibrationXpostion;
        public double _AFCalibrationZpostion;
        public double _AFCalibrationTpostion;
        /// <summary>
        /// Wafer尺寸 6 8 12
        /// </summary>
        public int _WaferSize = -1;
        /// <summary>
        /// 扫描等级 高精度1 高速2
        /// </summary>
        public int _ScanGrade = -1;
        /// <summary>
        /// 工作的通道数：四位二进制数从低位到到高位 明场 暗场1 暗场2 暗场3 1代表使用 0代表不使用
        /// F2000：两个通道都使用 0011 = 3
        /// F3000：四个通道都使用 1111 = 15
        /// </summary>
        public int _ChannelMode;
        /// <summary>
        /// 产品种类：F20001:1 F3000:2
        /// </summary>
        public int _MachineType;
        public bool Compare(StageRunPara tem) 
        {
            if(this._WaferSize != tem._WaferSize
                || this._ScanGrade != tem._ScanGrade
                || this._MachineType != tem._MachineType
                )
                return false;
            else return true;
        }
        public string _ScriptVersion = "AKStageLibVersion:1.0.0";
        /// <summary>
        /// 用于停靠接近Pin时的Z的位置
        /// </summary>
        public double _ZUpToPinPos = 0;
        public double _ZUpToPinVel1 = 0;
        public double _ZUpToPinVel2 = 0;

        public double _ZDownToPinPos = 0;
        public double _ZDownToPinVel1 = 0;
        public double _ZDownToPinVel2 = 0;
        /// <summary>
        /// 螺旋强制停止位置
        /// </summary>
        public double _StopTPos = 0;
        /// <summary>
        /// 尺寸兼容规格
        /// </summary>
        public int _CompatibleWaferSize = 68;
        public double _TTriggerStartAngle = 0;
        /// <summary>
        /// Z轴预聚焦补偿
        /// </summary>
        public double _AFCompensation = 0;
        /// <summary>
        /// 临时替代实时的大颗粒识别流程
        /// </summary>
        public int _ParticleDataNum = 0;
        public int _ParticleDataBegin = 221;
        public int _APPDataSnapFlag = 0;
        public int _APPDataSaveFlag = 0;
        public string _APPDataSavePath = null;
        public int _ScanCountForAppData = 0;
    }
    public class StageIOPara
    {
        /// <summary>
        /// 正压监测IO
        /// </summary>
        public int _TairPressure;
        //public int _XairPressure;
        /// <summary>
        /// PIN升降位置监测IO
        /// </summary>
        public int _PinUp;
        public int _PinDown;
        /// <summary>
        /// Wafer有无监测IO
        /// </summary>
        public int _WaferExist;
        /// <summary>
        /// 吸附WaferIO
        /// </summary>
        public int _Fix;
        //public int _Release;
        /// <summary>
        /// 升降PIN IO
        /// </summary>
        public int _PinControl;
        /// <summary>
        /// 针对电动气缸双IO控制
        /// </summary>
        public int _PinControlDown;
        /// <summary>
        /// AF光源控制IO
        /// </summary>
        public int _AFLightControl;
        /// <summary>
        /// 负压监测IO
        /// </summary>
        public int _VacPressure;
        /// <summary>
        /// 运动开始结束IO
        /// </summary>
        public int _SpiralRunFlag;
        /// <summary>
        /// 轴反馈AF电压的模拟IO
        /// </summary>
        public int _AFVIO = 0;
        /// <summary>
        /// AFSum值
        /// </summary>
        public int _AFSumVIO = 0;
        /// <summary>
        /// EFEMInterLock输出
        /// </summary>
        public int _EFEMInterLockOut;
        /// <summary>
        /// EFEMInterLock输入
        /// </summary>
        public int _EFEMInterLokcIn;
        /// <summary>
        /// 打开检测腔室门用于EFEM机械手取放料
        /// </summary>
        public int _InspectDoorOpenControl;
        /// <summary>
        /// 关闭检测腔室门
        /// </summary>
        public int _InspectDoorCloseControl;
        /// <summary>
        /// 检测腔室门开监测
        /// </summary>
        public int _InspectDoorOpen;
        /// <summary>
        /// 检测腔室门关监测
        /// </summary>
        public int _InspectDoorClose;
        /// <summary>
        /// 不同尺寸Chuck PIN位置切换
        /// </summary>
        public int _PinWithSizePosChangeControl;
        public int _PinWithSizePosChangeBigControl;
        public int _PinWithSizePosChangeSmallControl;
        /// <summary>
        /// Pin避让Z轴初始化
        /// </summary>
        public int _PinAvoidZInitPosChangeControl;
        public int _PinAvoidPosChangeControl;
        public int _PinNormalPosChangeControl;
        /// <summary>
        /// 一般适配两个2尺寸 6&8  or  8&12
        /// 6 or 8
        /// </summary>
        public int _PinWithSizePosSmall;
        /// <summary>
        /// 一般适配两个2尺寸 6&8  or  8&12
        /// 8 or 12
        /// </summary>
        public int _PinWithSizePosBig;
        /// <summary>
        /// Pin避让位置IO
        /// </summary>
        public int _PinAvoidZInitPos;
        /// <summary>
        /// Pin正常位置IO
        /// </summary>
        public int _PinNormalPos;
        /// <summary>
        /// 双尺寸兼容大尺寸对应的检测IO
        /// </summary>
        public int _BigWaferExist;

        public bool Compare(StageIOPara tem) 
        {
            if (this == tem) 
                return true;
            else
                return false;
        }

    }
    public enum GlobalInfo//与脚本里的序列保持一致
    {
        // arrange rGlobalVar to set initialvalue from index 100 start
        gFOV = 100,
        gWaferWaferRadius = 101,
        gSensorToOriginal = 102,
        gPixelSize = 103,
        gBinning = 104,
        gZinspect = 105,
        gXstart = 106,
        gZstart = 107,
        gTstart  = 108, // PinUpDownPos 
        gPixelCount = 109,
        gZDownPos = 110,
        //gStartFirst = 109,
        //gStopFirst = 110,
        //gStartSecond = 111,
        //gStopSecond = 112,
        gCameraLR = 113,
        gAFV = 114,
        gAFLimitUp = 115,
        gAFLimitDown = 116,
        gAFGainK = 117,
        gAFGaink1 = 118,
        gPVTStopDistance = 119,
        gPVTStopTime = 120,
        gCircleAngleStart = 121, //121---140
        gCircleFqStart = 141, //141---160

        gCircleNum = 171,
        gCircleDistance = 172,
        gAFSumThreshold = 173,
        gStopTPos = 180,
        gTTriggerStartAngle = 190,
        gStopDataSnap = 131
    }
    /// <summary>
    /// 用Z轴驱动器上的公用IO
    /// </summary>
    public enum StageOutPutIO
    {
        PinControl = 0,
        Fix,
        Release,
        AFControl
    }
    /// <summary>
    /// 与脚本保持一致，用于全局变量设置IO
    /// </summary>
    public enum GlobalinfoI
    {
        //arrange IGlobal from 100
        gPinUpPosIO  = 100,//3//100//3
        gPinDownPosIO = 101,//2//101//2
        gPinControlIO = 102,//0//102//0
        gWaferIO = 103,//0//103//0
        gAirIO = 104,//4
        gAutofocus = 105,//1//105//1
        gSpiralStart = 106,//7 //106
        gAFLightControl = 107,// 107
        gVacIO = 108,//1 //108
        gAdsorbControlIO = 109,
        gEFEMInterLockOut = 110,
        gEFEMInterLockIn = 111,
        gScanWithWafer = 116,
        gState = 120, // 0:Normal
        gPLCControl = 118,
        gBFCalControl = 117,
        gInspectDoorOpenControl = 112,//联动
        gInspectDoorCloseControl = 113,//联动
        ginspectDoorOpen = 114,
        gInspectDoorClose = 115,
        gConcurrence = 119,
        gStopInspectAF = 121,
        gStop = 130,
        gStopDataSnap = 131,
        gSaveAppData = 132
    }
    public enum GlobalinfoStr
    {
        gErrorInfoIndex = 5,
        gScriptVersion = 20,
        gAppSaveDataPath = 10
    }
    /// <summary>
    /// 上位机直接调用
    /// </summary>
    public enum StageInputIO
    {
        TairPressure = 4,
        XairPressure,
        PinUpPos = 3,
        PinDownPos = 2,
        WaferExist = 0
    }
    public enum StageErrorInfoZ 
    {
        正常 = 0,
        晶圆支撑升降故障 = 1,//升降PIN故障，PIN没有升降到位
                             //气缸的对应位置传感器没有感应到。
                             //升降气缸气压供应不足。
                             //升降电缸对应位置传感器没有感应到。升降电缸故障。
                             //处理措施：调整升降气缸气压，调整升降气缸位置感应传感器，调整电缸升降位置。
        扫描检测无晶圆 = 2, //扫描时没有检测到晶圆
                            //检查是否有晶圆，调整感应晶圆有无传感器
        晶圆吸附故障 = 3,   //晶圆吸附异常，调整负压气路和阈值
        扫描检测有晶圆 = 4, //设置无晶圆扫描发现有晶圆，检查是否有晶圆，调整感应晶圆有无传感器
        正压故障 = 5,       //设备供应正压异常，检查设备正压进气以及正压气路
        连接Stage故障 = 6,//运动平台控制器连接异常，检查网络连接和线路
        触发EFEM互锁 = 7,    //EFEM互锁信号被触发
                             //检查EFEM互锁信号线路是否正常，检查搬运取放片是否正常
        系统参数未设置 = 8, // 没有设置系统参数，检查主检配方流程。
        检测腔室开关门故障 = 9,//检查腔体门开闭故障，检查开关门控制IO状态是否正常，检查开关门位置传感器是否正常
        运动平台没有初始化 = 10,//运动平台没有初始化，主检进行运动平台初始化操作
        自动聚焦校准参数异常 = 11,//自动聚焦异常，聚焦得到的位置偏差大于0.5mm，检查聚焦参数的正确性或者重新获取校准获取聚焦参数
        晶圆释放故障 = 12, //晶圆释放异常，调整负压气路和阈值
        Stage扫描故障 = 13,// Stage扫描脚本运行时出现故障
        Stage控制器没有创建 = 14,// Stage控制器是空的
        Stage正在扫描中 = 15,//Stage正在扫描中，又收到扫描指令，需等待扫描完成
        改变PIN尺寸位置故障 = 16,
        改变PIN避让位置故障 = 17,
        Pin避让位置异常 = 18,
        Pin尺寸位置异常 = 19,
        大颗粒数量超出范围 = 20
    }
    public enum StageErrorInfoE 
    {
        Normal = 0,
        WaferPinUpDownFault = 1,
        ScanWithoutWafer = 2,
        FixWaferFault = 3,
        ScanWithWafer = 4,
        AirFault = 5,
        ConnectStageFault = 6,
        TriggerEFEMInterLock = 7,
        SystemParaNotSet = 8,
        DetectionChamberOpenCloseDoorFault = 9,
        StageNotInitialize = 10,
        AutoFocusCalibrationParaAbnormal = 11,
        ReleaseWaferFault = 12,
        StageScanFault = 13,
        StageControllerIsNull = 14,
        StageIsScanning = 15,
        ChangePinSizePostionFault = 16,
        ChangePinAvoidPostionFault = 17,
        PinAvoidPositionFault = 18,
        PinSizePositionFault = 19,
        BigParticleNumOutofRange = 20,
    }
    static class StageErrorInfoEE
    {
        public static string[] StageErrorInfos = new string[]
        {
        "Normal",
        "Wafer Pin Up Down Fault",
        "Scan Without Wafer",
        "Fix Wafer Fault",
        "Scan With Wafer",
        "Air Fault",
        "Connect Stage Fault",
        "Trigger EFEM InterLock",
        "System Para Not Set",
        "Detection Chamber Open Close Door Fault",
        "Stage Not Initialize",
        "AutoFocus Calibration Para Abnormal",
        "Release Wafer Fault",
        "Stage Scan Fault",
        "Stage Controller Is Null",
        "Stage Is Scanning",
        "ChangePinPostionFault",
        "ChangePinAvoidPostionFault",
        "PinAvoidPositionFault",
        "PinSizePositionFault",
        "BigParticleNumOutofRange"
        };
    }
    public enum WaferUpDownMode
    {
        Undefined,
        UpDownPinInChhuck,//Pin在Chuck内部，升降PIN
        UpDownPinOutChuck,//Pin在Chuck外部，升降PIN
        UpDownChuckFixPinNoAvoid,//升降CHuck，无避让
        UpDownFixPinAndChuck, //无Pin，Chuck固定内部有空间进行取放
        UpDownChuckFixPin,//Pin在Chuck外部，升降Chuck
        UpDownChuckFixPinWithSize,//Pin伴随尺寸移动
        //UpDownEdgeClamp,//边缘夹持，背面无接触


    }
    public enum LanguageMode 
    {
        EN = 1,
        CH
    }

    //public enum AxisFault
    //{
    //    //
    //    // 摘要:
    //    //     No bits set.
    //    None = 0x0,
    //    //
    //    // 摘要:
    //    //     The absolute value of the difference between the position command and the position
    //    //     feedback exceeded the threshold specified by the PositionErrorThreshold parameter.
    //    PositionErrorFault = 0x1,
    //    //
    //    // 摘要:
    //    //     The average motor current exceeded the threshold specified by the AverageCurrentThreshold
    //    //     and AverageCurrentTime parameters.
    //    OverCurrentFault = 0x2,
    //    //
    //    // 摘要:
    //    //     The axis encountered the clockwise (positive) end-of-travel limit switch.
    //    CwEndOfTravelLimitFault = 0x4,
    //    //
    //    // 摘要:
    //    //     The axis encountered the counter-clockwise (negative) end-of-travel limit switch.
    //    CcwEndOfTravelLimitFault = 0x8,
    //    //
    //    // 摘要:
    //    //     The axis was commanded to move beyond the position specified by the SoftwareLimitHigh
    //    //     parameter.
    //    CwSoftwareLimitFault = 0x10,
    //    //
    //    // 摘要:
    //    //     The axis was commanded to move beyond the position specified by the SoftwareLimitLow
    //    //     parameter.
    //    CcwSoftwareLimitFault = 0x20,
    //    //
    //    // 摘要:
    //    //     The amplifier for this axis exceeded its maximum current rating or experienced
    //    //     an internal error.
    //    AmplifierFault = 0x40,
    //    //
    //    // 摘要:
    //    //     The drive detected a problem with the feedback device specified by the FeedbackInput0
    //    //     parameter. Or, the drive detected an invalid feedback configuration.
    //    FeedbackInput0Fault = 0x80,
    //    //
    //    // 摘要:
    //    //     The drive detected a problem with the feedback device specified by the FeedbackInput1
    //    //     parameter. Or, the drive detected an invalid feedback configuration.
    //    FeedbackInput1Fault = 0x100,
    //    //
    //    // 摘要:
    //    //     The drive detected an invalid state (all high or all low) for the Hall-effect
    //    //     sensor inputs on this axis.
    //    HallSensorFault = 0x200,
    //    //
    //    // 摘要:
    //    //     The commanded velocity is more than the velocity command threshold. Before the
    //    //     axis is homed, this threshold is specified by the VelocityCommandThresholdBeforeHome
    //    //     parameter. After the axis is homed, this threshold is specified by the VelocityCommandThreshold
    //    //     parameter.
    //    MaxVelocityCommandFault = 0x400,
    //    //
    //    // 摘要:
    //    //     The emergency stop sense input, specified by the ESTOPFaultInput or SoftwareESTOPInput
    //    //     parameter, was triggered, or the controller detected a fault condition in the
    //    //     Safe Torque Off (STO) hardware.
    //    EmergencyStopFault = 0x800,
    //    //
    //    // 摘要:
    //    //     The absolute value of the difference between the velocity command and the velocity
    //    //     feedback exceeded the threshold specified by the VelocityErrorThreshold parameter.
    //    VelocityErrorFault = 0x1000,
    //    //
    //    // 摘要:
    //    //     The external fault input, specified by the ExternalFaultAnalogInput, ExternalFaultDigitalInput,
    //    //     or SoftwareExternalFaultInput parameter, was triggered.
    //    ExternalFault = 0x8000,
    //    //
    //    // 摘要:
    //    //     The motor thermistor input was triggered, which indicates that the motor exceeded
    //    //     its maximum recommended operating temperature.
    //    MotorTemperatureFault = 0x20000,
    //    //
    //    // 摘要:
    //    //     The amplifier temperature is not within the operating range or the shunt resistor
    //    //     temperature has exceeded the maximum threshold. This fault occurs at amplifier
    //    //     temperatures less than 0° C or greater than 75° C and shunt resistor temperatures
    //    //     greater than 200° C.
    //    AmplifierTemperatureFault = 0x40000,
    //    //
    //    // 摘要:
    //    //     The encoder fault input on the motor feedback connector was triggered.
    //    EncoderFault = 0x80000,
    //    //
    //    // 摘要:
    //    //     The position command or position feedback of the rotary gantry axis exceeded
    //    //     the value specified by the GantryMisalignmentThreshold parameter.
    //    GantryMisalignmentFault = 0x400000,
    //    //
    //    // 摘要:
    //    //     The difference between the position feedback and the scaled (adjusted by GainKv)
    //    //     velocity feedback exceeds the threshold specified by the PositionErrorThreshold
    //    //     parameter.
    //    FeedbackScalingFault = 0x800000,
    //    //
    //    // 摘要:
    //    //     The distance that the axis moved while searching for the marker exceeded the
    //    //     threshold specified by the MarkerSearchThreshold parameter.
    //    MarkerSearchFault = 0x1000000,
    //    //
    //    // 摘要:
    //    //     The axis decelerated to a stop because the motion violated a safe zone.
    //    SafeZoneFault = 0x2000000,
    //    //
    //    // 摘要:
    //    //     The axis did not achieve in position status in the period specified by the InPositionDisableTimeout
    //    //     parameter.
    //    InPositionTimeoutFault = 0x4000000,
    //    //
    //    // 摘要:
    //    //     The commanded voltage output exceeded the value of the PiezoVoltageClampLow or
    //    //     PiezoVoltageClampHigh parameter.
    //    VoltageClampFault = 0x8000000,
    //    //
    //    // 摘要:
    //    //     The motor power supply output has exceeded the allowable power or temperature
    //    //     threshold.
    //    MotorSupplyFault = 0x10000000,
    //    //
    //    // 摘要:
    //    //     The drive encountered an internal error that caused it to disable. Contact Aerotech
    //    //     Global Technical Support.
    //    InternalFault = 0x40000000
    //}
    public class StageTest 
    {
        public SpiralStageAerotech stage = new SpiralStageAerotech();
        //传入运行配置参数
        //LoadParaToStage();
        //初始化连接
        //STAGE_INITIALIZE();
        //回零到上下料位置:回零在回零点后会自动至上下料位置，
        //如果回零时有料，则吸附后再做动作，回零至初始位置后，释放物料
        //Home()
        //判断是否有晶圆:后续逻辑由调用层决定
        //IsWaferExist()

        //如果需要获取螺旋+同心圆 频率和角度信息，需要初始化后进行一次脚本运行，运行一次后通过参数接口获取频率和角度信息
        //频率信息需要给到PLC，角度信息需要给到算法同时保存至配置Recipe，后续进行正常的操作运行时需要把角度信息传入
        //运行脚本：脚本运行完毕后会自动到下料端并升PIN松片
    }
}
