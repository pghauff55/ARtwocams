/*
 *

TwoCams by Pamela Hauff 14-06-2018 

pamela.hauff@gmail.com

Creative Commons Attribution-NonCommercial 3.0 Australia (CC BY-NC 3.0 AU)


 *
 */

// ============================================================================
//	Includes
// ============================================================================

#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include <errno.h>
#include <fcntl.h> 

#include <termios.h>

#ifdef _WIN32
#  define snprintf _snprintf
#  define _USE_MATH_DEFINES
#endif
#include <stdlib.h>					// malloc(), free()
#include <math.h>
#ifdef __APPLE__
#  include <GLUT/glut.h>
#else
#  include <GL/glut.h>
#endif
#include <AR/config.h>
#include <AR/video.h>
#include <AR/param.h>			// arParamDisp()
#include <AR/ar.h>
#include <AR/gsub_lite.h>
#include <ARUtil/time.h>


#include <glm/gtx/transform.hpp> 
#include <glm/gtc/type_ptr.hpp>
// ============================================================================
//	Constants
// ============================================================================

#define VIEW_SCALEFACTOR		1.0         // Units received from ARToolKit tracking will be multiplied by this factor before being used in OpenGL drawing.
#define VIEW_DISTANCE_MIN		40.0        // Objects closer to the camera than this will not be displayed. OpenGL units.
#define VIEW_DISTANCE_MAX		10000.0     // Objects further away from the camera than this will not be displayed. OpenGL units.

// ============================================================================
//	Global variables
// ============================================================================


float XPos=0.0,ZPos=0.0;

// Preferences.
static int prefWindowed = TRUE;             // Use windowed (TRUE) or fullscreen mode (FALSE) on launch.
static int prefWidth = 1280;					// Initial window width, also updated during program execution.
static int prefHeight = 480;                // Initial window height, also updated during program execution.
static int prefDepth = 32;					// Fullscreen mode bit depth.
static int prefRefresh = 0;					// Fullscreen mode refresh rate. Set to 0 to use default rate.

static int          gARTImageSavePlease = FALSE;

// Marker detection.
static ARHandle		*gARHandle = NULL;
static ARHandle		*gARHandle2 = NULL;
static ARPattHandle	*gARPattHandle;
static ARPattHandle	*gARPattHandle2;

static long			gCallCountMarkerDetect = 0;

// Transformation matrix retrieval.
static AR3DHandle	*gAR3DHandle = NULL;
static AR3DHandle	*gAR3DHandle2 = NULL;

static ARdouble		gPatt_width     = 44.0;	// Per-marker, but we are using only 1 marker.
static ARdouble		gPatt_trans[3][4];	
static ARdouble		gPatt_trans2[3][4];
static int			gPatt_found = FALSE;	// Per-marker, but we are using only 1 marker.
static int			gPatt_found2 = FALSE;
static int			gPatt_id[4];				// Per-marker, but we are using only 1 marker.
static int			gPatt_id2[4];
float markerposx[4];
float markerposz[4];
static AR2VideoParamT *gVid1 =NULL;
static AR2VideoParamT *gVid2 =NULL;

// Drawing.
static int gWindowW=prefWidth;
static int gWindowH=prefHeight;
static ARParamLT *gCparamLT = NULL;
static ARGL_CONTEXT_SETTINGS_REF gArglSettings = NULL;
static ARParamLT *gCparamLT2 = NULL;
static ARGL_CONTEXT_SETTINGS_REF gArglSettings2 = NULL;
static int gShowHelp = 1;
static int gShowMode = 1;
static int gDrawRotate = FALSE;
static float gDrawRotateAngle = 0;			// For use in drawing.
char mytext[512];
int FD;
// ============================================================================
//	Function prototypes.
// ============================================================================

static void print(const char *text, const float x, const float y, int calculateXFromRightEdge, int calculateYFromTopEdge);
static void drawBackground(const float width, const float height, const float x, const float y);
static void printHelpKeys();
static void printMode();

// ============================================================================
//	Functions
// ============================================================================
int
set_interface_attribs (int fd, int speed, int parity)
{
        struct termios tty;
        memset (&tty, 0, sizeof tty);
        if (tcgetattr (fd, &tty) != 0)
        {
                printf ("error %d from tcgetattr", errno);
                return -1;
        }

        cfsetospeed (&tty, speed);
        cfsetispeed (&tty, speed);

        tty.c_cflag = (tty.c_cflag & ~CSIZE) | CS8;     // 8-bit chars
        // disable IGNBRK for mismatched speed tests; otherwise receive break
        // as \000 chars
        tty.c_iflag &= ~IGNBRK;         // disable break processing
        tty.c_lflag = 0;                // no signaling chars, no echo,
                                        // no canonical processing
        tty.c_oflag = 0;                // no remapping, no delays
        tty.c_cc[VMIN]  = 0;            // read doesn't block
        tty.c_cc[VTIME] = 5;            // 0.5 seconds read timeout

        tty.c_iflag &= ~(IXON | IXOFF | IXANY); // shut off xon/xoff ctrl

        tty.c_cflag |= (CLOCAL | CREAD);// ignore modem controls,
                                        // enable reading
        tty.c_cflag &= ~(PARENB | PARODD);      // shut off parity
        tty.c_cflag |= parity;
        tty.c_cflag &= ~CSTOPB;
        tty.c_cflag &= ~CRTSCTS;

        if (tcsetattr (fd, TCSANOW, &tty) != 0)
        {
                printf("error %d from tcsetattr", errno);
                return -1;
        }
        return 0;
}

void
set_blocking (int fd, int should_block)
{
        struct termios tty;
        memset (&tty, 0, sizeof tty);
        if (tcgetattr (fd, &tty) != 0)
        {
               printf("error %d from tggetattr", errno);
                return;
        }

        tty.c_cc[VMIN]  = should_block ? 1 : 0;
        tty.c_cc[VTIME] = 5;            // 0.5 seconds read timeout

        if (tcsetattr (fd, TCSANOW, &tty) != 0)
                printf ("error %d setting term attributes", errno);
}



// Something to look at, draw a rotating colour cube.
static void DrawCube(void)
{
    // Colour cube data.
    int i;
	float fSize = 40.0f;
    const GLfloat cube_vertices [8][3] = {
        /* +z */ {0.5f, 0.5f, 0.5f}, {0.5f, -0.5f, 0.5f}, {-0.5f, -0.5f, 0.5f}, {-0.5f, 0.5f, 0.5f},
        /* -z */ {0.5f, 0.5f, -0.5f}, {0.5f, -0.5f, -0.5f}, {-0.5f, -0.5f, -0.5f}, {-0.5f, 0.5f, -0.5f} };
    const GLubyte cube_vertex_colors [8][4] = {
        {255, 255, 255, 255}, {255, 255, 0, 255}, {0, 255, 0, 255}, {0, 255, 255, 255},
        {255, 0, 255, 255}, {255, 0, 0, 255}, {0, 0, 0, 255}, {0, 0, 255, 255} };
    const GLubyte cube_faces [6][4] = { /* ccw-winding */
        /* +z */ {3, 2, 1, 0}, /* -y */ {2, 3, 7, 6}, /* +y */ {0, 1, 5, 4},
        /* -x */ {3, 0, 4, 7}, /* +x */ {1, 2, 6, 5}, /* -z */ {4, 5, 6, 7} };
    
    glPushMatrix(); // Save world coordinate system.
    glRotatef(gDrawRotateAngle, 0.0f, 0.0f, 1.0f); // Rotate about z axis.
    glScalef(fSize, fSize, fSize);
    glTranslatef(0.0f, 0.0f, 0.5f); // Place base of cube on marker surface.
    glDisable(GL_LIGHTING);
    glDisable(GL_TEXTURE_2D);
    glDisable(GL_BLEND);
    glColorPointer(4, GL_UNSIGNED_BYTE, 0, cube_vertex_colors);
    glVertexPointer(3, GL_FLOAT, 0, cube_vertices);
    glEnableClientState(GL_VERTEX_ARRAY);
    glEnableClientState(GL_COLOR_ARRAY);
    for (i = 0; i < 6; i++) {
        glDrawElements(GL_TRIANGLE_FAN, 4, GL_UNSIGNED_BYTE, &(cube_faces[i][0]));
    }
    glDisableClientState(GL_COLOR_ARRAY);
    glColor4ub(0, 0, 0, 255);
    for (i = 0; i < 6; i++) {
        glDrawElements(GL_LINE_LOOP, 4, GL_UNSIGNED_BYTE, &(cube_faces[i][0]));
    }
    glPopMatrix();    // Restore world coordinate system.
}

static void DrawCubeUpdate(float timeDelta)
{
	if (gDrawRotate) {
		gDrawRotateAngle += timeDelta * 45.0f; // Rotate cube at 45 degrees per second.
		if (gDrawRotateAngle > 360.0f) gDrawRotateAngle -= 360.0f;
	}
}

static void usage(char *com)
{
    ARLOG("Usage: %s [options]\n", com);
    ARLOG("Options:\n");
    ARLOG("  --vconf <video parameter for the camera>\n");
    ARLOG("  --cpara <camera parameter file for the camera>\n");
    ARLOG("  -cpara=<camera parameter file for the camera>\n");
    ARLOG("  --width w     Use display/window width of w pixels.\n");
    ARLOG("  --height h    Use display/window height of h pixels.\n");
    ARLOG("  --refresh f   Use display refresh rate of f Hz.\n");
    ARLOG("  --windowed    Display in window, rather than fullscreen.\n");
    ARLOG("  --fullscreen  Display fullscreen, rather than in window.\n");
    ARLOG("  -h -help --help: show this message\n");
    exit(0);
}

static int setupCamera(const char *cparam_name, char *vconf, ARParamLT **cparamLT_p, ARHandle **arhandle, AR3DHandle **ar3dhandle,AR2VideoParamT **gVid)
{	
    ARParam			cparam;
	int				xsize, ysize;
    AR_PIXEL_FORMAT pixFormat;

    // Open the video path.
    if ((*gVid=ar2VideoOpen(vconf)) ==NULL) {
    	ARLOGe("setupCamera(): Unable to open connection to camera.\n");
    	return (FALSE);
	}
	
    // Find the size of the window.
    if (ar2VideoGetSize(*gVid,&xsize, &ysize) < 0) {
        ARLOGe("setupCamera(): Unable to determine camera frame size.\n");
        ar2VideoClose(*gVid);
        return (FALSE);
    }
    ARLOGi("Camera image size (x,y) = (%d,%d)\n", xsize, ysize);
	
	// Get the format in which the camera is returning pixels.
	pixFormat = ar2VideoGetPixelFormat(*gVid);
	if (pixFormat == AR_PIXEL_FORMAT_INVALID) {
    	ARLOGe("setupCamera(): Camera is using unsupported pixel format.\n");
       ar2VideoClose(*gVid);
		return (FALSE);
	}
	
	// Load the camera parameters, resize for the window and init.
	if (cparam_name && *cparam_name) {
        if (arParamLoad(cparam_name, 1, &cparam) < 0) {
		    ARLOGe("setupCamera(): Error loading parameter file %s for camera.\n", cparam_name);
          ar2VideoClose(*gVid);
            return (FALSE);
        }
    } else {
        arParamClearWithFOVy(&cparam, xsize, ysize, M_PI_4); // M_PI_4 radians = 45 degrees.
        ARLOGw("Using default camera parameters for %dx%d image size, 45 degrees vertical field-of-view.\n", xsize, ysize);
    }
    if (cparam.xsize != xsize || cparam.ysize != ysize) {
        ARLOGw("*** Camera Parameter resized from %d, %d. ***\n", cparam.xsize, cparam.ysize);
        arParamChangeSize(&cparam, xsize, ysize, &cparam);
    }
#ifdef DEBUG
    ARLOG("*** Camera Parameter ***\n");
    arParamDisp(&cparam);
#endif
    if ((*cparamLT_p = arParamLTCreate(&cparam, AR_PARAM_LT_DEFAULT_OFFSET)) == NULL) {
        ARLOGe("setupCamera(): Error: arParamLTCreate.\n");
        return (FALSE);
    }

    if ((*arhandle = arCreateHandle(*cparamLT_p)) == NULL) {
        ARLOGe("setupCamera(): Error: arCreateHandle.\n");
        return (FALSE);
    }
    if (arSetPixelFormat(*arhandle, pixFormat) < 0) {
        ARLOGe("setupCamera(): Error: arSetPixelFormat.\n");
        return (FALSE);
    }
	if (arSetDebugMode(*arhandle, AR_DEBUG_DISABLE) < 0) {
        ARLOGe("setupCamera(): Error: arSetDebugMode.\n");
        return (FALSE);
    }
	if ((*ar3dhandle = ar3DCreateHandle(&cparam)) == NULL) {
        ARLOGe("setupCamera(): Error: ar3DCreateHandle.\n");
        return (FALSE);
    }
	
	if (ar2VideoCapStart(*gVid) != 0) {
    	ARLOGe("setupCamera(): Unable to begin camera data capture.\n");
		return (FALSE);		
	}
	
	return (TRUE);
}

static int setupMarker(const char *patt_name, int *patt_id, ARHandle *arhandle, ARPattHandle **pattHandle_p)
{	
    if ((*pattHandle_p = arPattCreateHandle()) == NULL) {
        ARLOGe("setupMarker(): Error: arPattCreateHandle.\n");
        return (FALSE);
    }
    
	// Loading only 1 pattern in this example.
	if ((*patt_id = arPattLoad(*pattHandle_p, patt_name)) < 0) {
		ARLOGe("setupMarker(): Error loading pattern file %s.\n", patt_name);
		arPattDeleteHandle(*pattHandle_p);
		return (FALSE);
	}
    
    arPattAttach(arhandle, *pattHandle_p);
	
	return (TRUE);
}

static void cleanup(void)
{
  close(FD);
	arglCleanup(gArglSettings);
	arglCleanup(gArglSettings2);
    gArglSettings = NULL;
	arPattDetach(gARHandle);
arPattDetach(gARHandle2);
	arPattDeleteHandle(gARPattHandle);
	arPattDeleteHandle(gARPattHandle2);
	
ar2VideoCapStop(gVid1);
	ar2VideoCapStop(gVid2);  
	ar3DDeleteHandle(&gAR3DHandle);
	arDeleteHandle(gARHandle);
    arParamLTFree(&gCparamLT);
	ar3DDeleteHandle(&gAR3DHandle2);
	arDeleteHandle(gARHandle2);
    arParamLTFree(&gCparamLT2);

	ar2VideoClose(gVid1);
ar2VideoClose(gVid2);
}

static void Keyboard(unsigned char key, int x, int y)
{
	int mode, threshChange = 0;
    AR_LABELING_THRESH_MODE modea;
char buf[400];
	
	switch (key) {
		case 0x1B:						// Quit.
		case 'Q':
		case 'q':
			cleanup();
			exit(0);
			break;
		case ',':
			write (FD, "o20 45\n", 7);         

			usleep ((7 + 25) * 100);  
			// read (FD, buf, sizeof buf);	
			//printf("recv:%s",buf);
	
			break;
		case '.':
			write (FD, "o-20 45\n", 8);         

			usleep ((8 + 25) * 100);  
			// read (FD, buf, sizeof buf);	
			//printf("recv:%s",buf);
	
			break;

		case ' ':
			gDrawRotate = !gDrawRotate;
			break;
		case 'X':
		case 'x':
            arGetImageProcMode(gARHandle, &mode);
            switch (mode) {
                case AR_IMAGE_PROC_FRAME_IMAGE:  mode = AR_IMAGE_PROC_FIELD_IMAGE; break;
                case AR_IMAGE_PROC_FIELD_IMAGE:
                default: mode = AR_IMAGE_PROC_FRAME_IMAGE; break;
            }
            arSetImageProcMode(gARHandle, mode);
 arSetImageProcMode(gARHandle2, mode);
			break;
		case 'C':
		case 'c':
			ARLOGe("*** Camera - %f (frame/sec)\n", (double)gCallCountMarkerDetect/arUtilTimer());
			gCallCountMarkerDetect = 0;
			arUtilTimerReset();
			break;
		case 'a':
		case 'A':
			arGetLabelingThreshMode(gARHandle, &modea);
            switch (modea) {
                case AR_LABELING_THRESH_MODE_MANUAL:        modea = AR_LABELING_THRESH_MODE_AUTO_MEDIAN; break;
                case AR_LABELING_THRESH_MODE_AUTO_MEDIAN:   modea = AR_LABELING_THRESH_MODE_AUTO_OTSU; break;
                case AR_LABELING_THRESH_MODE_AUTO_OTSU:     modea = AR_LABELING_THRESH_MODE_AUTO_ADAPTIVE; break;
                case AR_LABELING_THRESH_MODE_AUTO_ADAPTIVE: modea = AR_LABELING_THRESH_MODE_AUTO_BRACKETING; break;
                case AR_LABELING_THRESH_MODE_AUTO_BRACKETING:
                default: modea = AR_LABELING_THRESH_MODE_MANUAL; break;
            }
            arSetLabelingThreshMode(gARHandle, modea);
  arSetLabelingThreshMode(gARHandle2, modea);//	
		break;
		case '-':
			threshChange = -5;
			break;
		case '+':
		case '=':
			threshChange = +5;
			break;
		case 'D':
		case 'd':
			arGetDebugMode(gARHandle, &mode);
			arSetDebugMode(gARHandle, !mode);
			arSetDebugMode(gARHandle2, !mode);

			break;
        case 's':
        case 'S':
            if (!gARTImageSavePlease) gARTImageSavePlease = TRUE;
            break;
		case '?':
		case '/':
            gShowHelp++;
            if (gShowHelp > 1) gShowHelp = 0;
			break;
        case 'm':
        case 'M':
            gShowMode = !gShowMode;
            break;
		default:
			break;
	}
	if (threshChange) {
		int threshhold;
		arGetLabelingThresh(gARHandle, &threshhold);
		threshhold += threshChange;
		if (threshhold < 0) threshhold = 0;
		if (threshhold > 255) threshhold = 255;
		arSetLabelingThresh(gARHandle, threshhold);
		arSetLabelingThresh(gARHandle2, threshhold);

	}
	
}
int patt_ID2=-1;
int patt_ID=-1;
int patt_cam=1;
static void mainLoop(void)
{
    static int imageNumber = 0;
	static int ms_prev;
	int ms;
	float s_elapsed;
	AR2VideoBufferT *image,*image2;
	ARdouble err;

    int             j, k;
	
	// Find out how long since mainLoop() last ran.
	ms = glutGet(GLUT_ELAPSED_TIME);
	s_elapsed = (float)(ms - ms_prev) * 0.001f;
	if (s_elapsed < 0.01f) return; // Don't update more often than 100 Hz.
	ms_prev = ms;
	
	// Update drawing.
	DrawCubeUpdate(s_elapsed);


	gCallCountMarkerDetect++; // Increment ARToolKit FPS counter.

	// Grab a video frame.
	if ((image = ar2VideoGetImage(gVid1)) != NULL) {
        
        arglPixelBufferDataUpload(gArglSettings, image->buff);

  
		
	
		
		// Detect the markers in the video frame.
		if (arDetectMarker(gARHandle, image) < 0) {
			exit(-1);
		}
		
		// Check through the marker_info array for highest confidence
		// visible marker matching our preferred pattern.
		k = -1;
		for (j = 0; j < gARHandle->marker_num; j++) {
			for(int patt_i=0;patt_i<4;patt_i++){
			if (gARHandle->markerInfo[j].id == gPatt_id[patt_i]) {
				if (k == -1){
					 k = j; // First marker detected.
					patt_ID=patt_i;
				}	
				else if (gARHandle->markerInfo[j].cf > gARHandle->markerInfo[k].cf){
					 k = j; // Higher confidence marker detected.
					patt_ID=patt_i;
				}
			}
			}
		}

		if (k != -1) {
			if(gAR3DHandle->icpHandle!=NULL){
			// Get the transformation between the marker and the real camera into gPatt_trans.
			err = arGetTransMatSquare(gAR3DHandle, &(gARHandle->markerInfo[k]), gPatt_width, gPatt_trans);
				///printf("err=%f\n",err);
			}
			patt_cam=1;
			gPatt_found = TRUE;
		} else {
			gPatt_found = FALSE;
		}
		
	}
if ((image2 = ar2VideoGetImage(gVid2)) != NULL) {
        
        arglPixelBufferDataUpload(gArglSettings2, image2->buff);

  	
	
		
		// Detect the markers in the video frame.
		if (arDetectMarker(gARHandle2, image2) < 0) {
			exit(-1);
		}
		
		// Check through the marker_info array for highest confidence
		// visible marker matching our preferred pattern.
		k = -1;
		for (j = 0; j < gARHandle2->marker_num; j++) {
			for(int patt_i=0;patt_i<4;patt_i++){
			if (gARHandle2->markerInfo[j].id == gPatt_id2[patt_i]) {
				if (k == -1){
					 k = j; // First marker detected.
					patt_ID2=patt_i;
				}	
				else if (gARHandle2->markerInfo[j].cf > gARHandle2->markerInfo[k].cf){
					 k = j; // Higher confidence marker detected.
					patt_ID2=patt_i;
				}
			}
			}
		}
		
		if (k != -1) {
			if(gAR3DHandle2->icpHandle!=NULL){
			// Get the transformation between the marker and the real camera into gPatt_trans.
			err = arGetTransMatSquare(gAR3DHandle2, &(gARHandle2->markerInfo[k]), gPatt_width, gPatt_trans2);
				///printf("err=%f\n",err);
			}
			gPatt_found2 = TRUE;
			patt_cam=2;
		} else {
			gPatt_found2 = FALSE;
		}
		
	}




glutPostRedisplay();
}

//
//	This function is called on events when the visibility of the
//	GLUT window changes (including when it first becomes visible).
//
static void Visibility(int visible)
{
	if (visible == GLUT_VISIBLE) {
		glutIdleFunc(mainLoop);
	} else {
		glutIdleFunc(NULL);
	}
}

//
//	This function is called when the
//	GLUT window is resized.
//
static void Reshape(int w, int h)
{
    gWindowW = w;
    gWindowH = h;
    
	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
	glViewport(0, 0, (GLsizei) w, (GLsizei) h);
	
	// Call through to anyone else who needs to know about window sizing here.
}

//
// This function is called when the window needs redrawing.
//
static void Display(void)
{
char text1[200];
char text2[200];
    ARdouble p[16];
	ARdouble m[16];
float x1=0.0,z1=0.0;
float x2=0.0,z2=0.0;

	
	// Select correct buffer for this context.
	glDrawBuffer(GL_BACK);
	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT); // Clear the buffers for new frame.
	glViewport((GLsizei)prefWidth/4.0, 0, (GLsizei) prefWidth/4.0, (GLsizei)prefHeight);
	arglDispImage(gArglSettings2);
	glViewport(0, 0, (GLsizei)prefWidth/4.0, (GLsizei) prefHeight);
	arglDispImage(gArglSettings);
				
	// Projection transformation.
	arglCameraFrustumRH(&(gCparamLT->param), VIEW_DISTANCE_MIN, VIEW_DISTANCE_MAX, p);
	glMatrixMode(GL_PROJECTION);
#ifdef ARDOUBLE_IS_FLOAT
    glLoadMatrixf(p);
#else
    glLoadMatrixd(p);
#endif
	glMatrixMode(GL_MODELVIEW);
		
	glEnable(GL_DEPTH_TEST);

	// Viewing transformation.
	glLoadIdentity();
	// Lighting and geometry that moves with the camera should go here.
	// (I.e. must be specified before viewing transformations.)
	//none
	float angle1,distance1,angle2,distance2;




	if (gPatt_found) {
	        
		// Calculate the camera position relative to the marker.
		// Replace VIEW_SCALEFACTOR with 1.0 to make one drawing unit equal to 1.0 ARToolKit units (usually millimeters).
		arglCameraViewRH((const ARdouble (*)[4])gPatt_trans, m, VIEW_SCALEFACTOR);
			glm::mat4 myMatrix=glm::make_mat4(m);
			glm::vec4 myVector(0.0f, 0.0f, 0.0f, 1.0f);
			glm::vec4 tv = myMatrix * myVector;
			glm::vec4 myVector2(0.0f, 0.0f, -1.0f, 0.0f);
			glm::vec4 tv2 = myMatrix * myVector2;


		int patt_num=-1;
	for(int patt_i=0;patt_i<4;patt_i++){
		if(patt_ID==gPatt_id[patt_i]){
			patt_num=patt_i;
		//printf("cam 1: %d\n",patt_i);
		}
	}
if(patt_num>=0 && patt_num<4){

x2=markerposx[patt_num];
z2=markerposz[patt_num];
}
 angle2=(180.0/M_PI)*atan2(tv[0],-tv[2]);
	 distance2=sqrt(tv[0]*tv[0]+(tv[2]+130.0)*(tv[2]+130.0));


	angle2=angle2-30.0;
	
 	

 //	snprintf(text1, sizeof(text1), "%f %f   %f  %f  id:%d %d\n %f %f\n",tv[0],tv[2],angle,distance,patt_num,patt_cam,XPos,ZPos);
 	

	#ifdef ARDOUBLE_IS_FLOAT
        glLoadMatrixf(m);
	#else
        glLoadMatrixd(m);
	#endif

		// All lighting and geometry to be drawn relative to the marker goes here.
		DrawCube();
	
	} // gPatt_found
	else {
		//snprintf(text1, sizeof(text1),"No Match                                               \n");
	}

	if (gPatt_found2) {
	        
		// Calculate the camera position relative to the marker.
		// Replace VIEW_SCALEFACTOR with 1.0 to make one drawing unit equal to 1.0 ARToolKit units (usually millimeters).
		arglCameraViewRH((const ARdouble (*)[4])gPatt_trans2, m, VIEW_SCALEFACTOR);
			glm::mat4 myMatrix=glm::make_mat4(m);
			glm::vec4 myVector(0.0f, 0.0f, 0.0f, 1.0f);
			glm::vec4 tv = myMatrix * myVector;
			glm::vec4 myVector2(0.0f, 0.0f, -1.0f, 0.0f);
			glm::vec4 tv2 = myMatrix * myVector2;


		int patt_num=-1;
	for(int patt_i=0;patt_i<4;patt_i++){
		if(patt_ID2==gPatt_id2[patt_i]){
		//printf("cam 2: %d\n",patt_i);
			patt_num=patt_i;
		}
	}
if(patt_num>=0 && patt_num<4){
x1=markerposx[patt_num];
z1=markerposz[patt_num];
}


	angle1=(180.0/M_PI)*atan2(tv[0],-tv[2]);
	 distance1=sqrt(tv[0]*tv[0]+(tv[2]+130.0)*(tv[2]+130.0));

	
	angle1=angle1+30.0;
  

 //	snprintf(text2, sizeof(text2), "%f %f   %f  %f  id:%d %d\n %f %f\n",tv[0],tv[2],angle2,distance2,patt_num,patt_cam,XPos,ZPos);
 	

	#ifdef ARDOUBLE_IS_FLOAT
        glLoadMatrixf(m);
	#else
        glLoadMatrixd(m);
	#endif

		// All lighting and geometry to be drawn relative to the marker goes here.
		DrawCube();
	
	} // gPatt_found
	else {
		//snprintf(text2, sizeof(text2),"No Match                                               \n");
	}


if (gPatt_found && gPatt_found2 ) {

float R=sqrt((x2-x1)*(x2-x1)+(z2-z1)*(z2-z1));


float a=(distance1*distance1-distance2*distance2)/(2*R*R);
float b=0.5*sqrt(2.0*(distance1*distance1+distance2*distance2)/(R*R)-(distance1*distance1-distance2*distance2)*(distance1*distance1-distance2*distance2)/(R*R*R*R)-1.0);

XPos=(x1+x2)/2.0+a*(x2-x1)-b*(z2-z1);
ZPos=(z1+z2)/2.0+a*(z2-z1)-b*(x1-x2);


snprintf(text1, sizeof(text1), " %f %f %f %f  ",distance1,distance2,XPos,ZPos);
 	


}


	// Any 2D overlays go here.
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    glOrtho(0, (GLdouble)gWindowW, 0, (GLdouble)gWindowH, -1.0, 1.0);
glViewport(0, 0, (GLsizei) prefWidth, (GLsizei)prefHeight);

    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();
    glDisable(GL_LIGHTING);
    glDisable(GL_DEPTH_TEST);

  print(text1, 2.0f,  (1 - 1)*24.0f + 2.0f, 0, 1);
// print(text2, 2.0f,  (2 - 1)*24.0f + 2.0f, 0, 1);


    glPointSize(4.0f);
   glBegin(GL_POINTS); //starts drawing of points
for(int ik=0;ik<4;ik++){
	glColor3f(1.0,1.0,1.0);
      glVertex2f(prefWidth*0.75f+markerposx[ik]*0.4f,prefHeight*0.5f+markerposz[ik]*0.4f);
   } 
    glEnd();//end drawing of points


   /* if (gShowMode) {
       // printMode();
    }
    if (gShowHelp) {
        if (gShowHelp == 1) {
            printHelpKeys();
        }
    }*/
	
	glutSwapBuffers();
}

int main(int argc, char** argv)
{
    char    glutGamemode[32] = "";
    char   *vconf = "-dev=/dev/video1";
    char   *cparam_name = NULL; //"/home/roverone/Desktop/artoolkit5-master/bin/cam_param.dat";
    int     i;
    int     gotTwoPartOption;
    char    patt_name[]  = "Data/hiro.patt";
    char    patt_name2[] ="patt1.dat";
 char    patt_name3[] ="/home/roverone/Desktop/artoolkit5-master/bin/patt2.dat";
char portname[]="/dev/ttyUSB0";
  


	markerposx[0]=-500.0;
	markerposz[0]=0.0;

	markerposx[1]=0.0;
	markerposz[1]=-500.0;

	markerposx[2]=500.0;
	markerposz[2]=0.0;

	markerposx[3]=0.0;
	markerposz[3]=500.0;


       printf("Opening serial port...\n");
	FD = open (portname, O_RDWR | O_NOCTTY | O_SYNC);
	if (FD < 0)
	{
        printf ("error %d opening %s: %s", errno, portname, strerror (errno));
        //return 0;
	}
	else {
	printf("serial port...open\n");
	set_interface_attribs (FD, B115200, 0);  // set speed to 115,200 bps, 8n1 (no parity)
	set_blocking (FD, 0);                // set no blocking
	char buf [400];
	 read (FD, buf, sizeof buf);	
	printf("recv:%s",buf);

usleep ((7 + 25) * 10000);  



write (FD, "o20 50\n", 7);         

usleep ((7 + 25) * 100);  
	 read (FD, buf, sizeof buf);	
	printf("recv:%s",buf);

	}

    
    glutInit(&argc, argv);
    
	//
	// Video setup.
	//ss

	if (!setupCamera(cparam_name,"-dev=/dev/video1 -width=640 -height=480", &gCparamLT, &gARHandle, &gAR3DHandle,&gVid1)) {
		ARLOGe("main(): Unable to set up AR camera.\n");
		exit(-1);
	}
	if (!setupCamera(cparam_name, "-dev=/dev/video0 -width=640 -height=480", &gCparamLT2, &gARHandle2, &gAR3DHandle2,&gVid2)) {
		ARLOGe("main(): Unable to set up AR camera.\n");
		exit(-1);
	}

	//
	// Graphics setup.
	//

	// Set up GL context(s) for OpenGL to draw into.
	glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGBA | GLUT_DEPTH);

		glutInitWindowSize(prefWidth, prefHeight);
		glutCreateWindow(argv[0]);
	

	// Setup ARgsub_lite library for current OpenGL context.
	if ((gArglSettings = arglSetupForCurrentContext(&(gCparamLT->param), ar2VideoGetPixelFormat(gVid1))) == NULL) {
		ARLOGe("main(): arglSetupForCurrentContext() returned error.\n");
		cleanup();
		exit(-1);
	}
	if ((gArglSettings2 = arglSetupForCurrentContext(&(gCparamLT2->param), ar2VideoGetPixelFormat(gVid2))) == NULL) {
		ARLOGe("main(): arglSetupForCurrentContext() returned error.\n");
		cleanup();
		exit(-1);
	}


    arglSetupDebugMode(gArglSettings, gARHandle);
    arglSetupDebugMode(gArglSettings2, gARHandle2);
	arUtilTimerReset();

printf("Loading patterns 1-4.\n");
		char patt_nameA[]="/Data/patt1.dat";

	if ((gARPattHandle= arPattCreateHandle()) == NULL) {
     	   ARLOGe("setupMarker(): Error: arPattCreateHandle.\n");
     	   return (FALSE);
    	}
	for(int patt_i=0;patt_i<4;patt_i++){
		// Load marker(s).
		patt_nameA[10]=49+patt_i;
		char filename[200];
		getcwd(filename,sizeof(filename));
    	    strcat(filename,patt_nameA);
		printf("%s\n",filename);
    
	
		if ((gPatt_id[patt_i]= arPattLoad(gARPattHandle, filename)) < 0) {
			ARLOGe("setupMarker(): Error loading pattern file %s.\n", filename);
			arPattDeleteHandle(gARPattHandle);
			return (FALSE);
		}
    
 
		printf("patt_id:(%d)\n",gPatt_id[patt_i]);
	}
  	 arPattAttach(gARHandle, gARPattHandle);


	if ((gARPattHandle2= arPattCreateHandle()) == NULL) {
     	   ARLOGe("setupMarker(): Error: arPattCreateHandle.\n");
     	   return (FALSE);
    	}
	for(int patt_i=0;patt_i<4;patt_i++){
		// Load marker(s).
		patt_nameA[10]=49+patt_i;
		char filename[200];
		getcwd(filename,sizeof(filename));
    	    strcat(filename,patt_nameA);
		printf("%s\n",filename);
    
	
		if ((gPatt_id2[patt_i]= arPattLoad(gARPattHandle2, filename)) < 0) {
			ARLOGe("setupMarker(): Error loading pattern file %s.\n", filename);
			arPattDeleteHandle(gARPattHandle2);
			return (FALSE);
		}
    
 
		printf("patt_id:(%d)\n",gPatt_id2[patt_i]);
	}
  	 arPattAttach(gARHandle2, gARPattHandle2);

	
	// Register GLUT event-handling callbacks.
	// NB: mainLoop() is registered by Visibility.
	glutDisplayFunc(Display);
	glutReshapeFunc(Reshape);
	glutVisibilityFunc(Visibility);
	glutKeyboardFunc(Keyboard);
	
	glutMainLoop();

	return (0);
}

//
// The following functions provide the onscreen help text and mode info.
//

static void print(const char *text, const float x, const float y, int calculateXFromRightEdge, int calculateYFromTopEdge)
{
    int i, len;
    GLfloat x0, y0;
    
    if (!text) return;
    
    if (calculateXFromRightEdge) {
        x0 = gWindowW - x - (float)glutBitmapLength(GLUT_BITMAP_TIMES_ROMAN_24 , (const unsigned char *)text);
    } else {
        x0 = x;
    }
    if (calculateYFromTopEdge) {
        y0 = gWindowH - y - 24.0f;
    } else {
        y0 = y;
    }
    glRasterPos2f(x0, y0);
    
    len = (int)strlen(text);
    for (i = 0; i < len; i++) glutBitmapCharacter(GLUT_BITMAP_TIMES_ROMAN_24 , text[i]);
}

static void drawBackground(const float width, const float height, const float x, const float y)
{
    GLfloat vertices[4][2];
    
    vertices[0][0] = x; vertices[0][1] = y;
    vertices[1][0] = width + x; vertices[1][1] = y;
    vertices[2][0] = width + x; vertices[2][1] = height + y;
    vertices[3][0] = x; vertices[3][1] = height + y;
    glLoadIdentity();
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glEnable(GL_BLEND);
    glVertexPointer(2, GL_FLOAT, 0, vertices);
    glEnableClientState(GL_VERTEX_ARRAY);
    glColor4f(0.0f, 0.0f, 0.0f, 0.5f);	// 50% transparent black.
    glDrawArrays(GL_TRIANGLE_FAN, 0, 4);
    glColor4f(1.0f, 1.0f, 1.0f, 1.0f); // Opaque white.
    //glLineWidth(1.0f);
    //glDrawArrays(GL_LINE_LOOP, 0, 4);
    glDisableClientState(GL_VERTEX_ARRAY);
    glDisable(GL_BLEND);
}

static void printHelpKeys()
{
    int i;
    GLfloat  w, bw, bh;
    const char *helpText[] = {
        "Keys:\n",
        " ? or /        Show/hide this help.",
        " q or [esc]    Quit program.",
        " d             Activate / deactivate debug mode.",
        " m             Toggle display of mode info.",
        " a             Toggle between available threshold modes.",
        " - and +       Switch to manual threshold mode, and adjust threshhold up/down by 5.",
        " x             Change image processing mode.",
        " c             Calulcate frame rate.",
    };
#define helpTextLineCount (sizeof(helpText)/sizeof(char *))
    
    bw = 0.0f;
    for (i = 0; i < helpTextLineCount; i++) {
        w = (float)glutBitmapLength(GLUT_BITMAP_HELVETICA_10, (unsigned char *)helpText[i]);
        if (w > bw) bw = w;
    }
    bh = helpTextLineCount * 10.0f /* character height */+ (helpTextLineCount - 1) * 2.0f /* line spacing */;
    drawBackground(bw, bh, 2.0f, 2.0f);
    
    for (i = 0; i < helpTextLineCount; i++) print(helpText[i], 2.0f, (helpTextLineCount - 1 - i)*12.0f + 2.0f, 0, 0);;
}

static void printMode()
{
    int len, thresh, line, mode, xsize, ysize;
    AR_LABELING_THRESH_MODE threshMode;
    ARdouble tempF;
    char   text[512],*text_p;

    glColor3ub(255, 255, 255);
    line = 1;
    
    // Image size and processing mode.
    ar2VideoGetSize(gVid1,&xsize, &ysize);
 
    snprintf(text, sizeof(text), "Processing %dx%d video frames %s", xsize, ysize, text_p);
    print(text, 2.0f,  (line - 1)*12.0f + 2.0f, 0, 1);
    line++;
    
    
    snprintf(text, sizeof(text), "Threshold mode: %s", text_p);
    if (threshMode != AR_LABELING_THRESH_MODE_AUTO_ADAPTIVE) {
        arGetLabelingThresh(gARHandle, &thresh);
        len = (int)strlen(text);
        snprintf(text + len, sizeof(text) - len, ", thresh=%d", thresh);
    }
    print(text, 2.0f,  (line - 1)*12.0f + 2.0f, 0, 1);
    line++;
    
    // Border size, image processing mode, pattern detection mode.
    arGetBorderSize(gARHandle, &tempF);
    snprintf(text, sizeof(text), "Border: %0.1f%%", tempF*100.0);
   
    len = (int)strlen(text);
    snprintf(text + len, sizeof(text) - len, ", Pattern detection mode: %s", text_p);
    print(text, 2.0f,  (line - 1)*12.0f + 2.0f, 0, 1);
    line++;
    
    // Window size.
    snprintf(text, sizeof(text), "Drawing into %dx%d window", gWindowW, gWindowH);
    print(text, 2.0f,  (line - 1)*12.0f + 2.0f, 0, 1);
    line++;
    
}
